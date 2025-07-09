open Sugar
open Language
open TypedCoreEff
open Rty
open Typing

(** Phase 1: Exhaustive program behavior inference/summarization following Syn* rules *)

let rec infer_pure opctx rctx (value : value typed) : rty =
  match value.x with
  | VConst c ->
      (* SynConst rule: Γ ⊢ c ↑ {b | ν = c} *)
      mk_rty_var_eq_c value.ty c
  | VVar x ->
      (* SynVar rule: Γ(x) = {b | φ} ⊢ x ↑ {b | ν = x} *)
      mk_rty_var_eq_var x #: value.ty
  | VLam { lamarg; lambody } ->
      (* SynFun rule: Γ, x:t ⊢ e ↑ τ ⟹ Γ ⊢ λx:t.e ↑ x:t → τ *)
      let rx = { rx = lamarg.x; rty = refine_to_ceil lamarg.ty } in
      let rctx' = RTypectx.new_to_right rctx rx in
      let tau = infer_eff opctx rctx' lambody in
      ArrRty { arr = NormalArr rx; rethty = Monad tau }
  | VFix _ -> _failatwith __FILE__ __LINE__ "unimp"
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

and infer_eff opctx rctx (expr : comp typed) : monad =
  match expr.x with
  | CVal v ->
      (* SynLift rule: Γ ⊢ v ↑ t, FT[r] = ret v ⟹ Γ ⊢ v ↑ M(t, FT[r]) *)
      let t = infer_pure opctx rctx v #: expr.ty in
      let ret = { rx = "ret"; rty = t } in
      { ret; eff = Eff.Atom Eff.Id }
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CAppOp { op; appopargs } ->
          (* Handle operator application *)
          let arg_rtys = List.map (fun arg -> infer_pure opctx rctx arg) appopargs in
          let locals, x_eff_ty = infer_op opctx rctx (arg_rtys, of_ty_pre rhs.ty (mk_any)) op in
          let xret = { rx = lhs.x; rty = x_eff_ty.ret.rty } in
          let rctx' = RTypectx.new_to_right rctx xret in
          let tau = infer_eff opctx rctx' letbody in
          (* Apply Exist instead of Abduce *)
          let tau_result = exist_quantify_monad rctx xret tau in
          let eff_bound = bind_effects x_eff_ty.eff tau_result.eff in
          multi_existential_monad locals { ret = tau_result.ret; eff = eff_bound }
      | _ ->
          (* SynLet rule: Γ ⊢ e_x ↑ M(t_x, FT_x), Γ,x:t_x ⊢ e ↑ τ, 
             Exist(Γ,x:t_x,τ) = M(t,FT), FT[r] = bind FT_x λx.FT *)
          let tau_x = infer_eff opctx rctx rhs in
          let xret = { rx = lhs.x; rty = tau_x.ret.rty } in
          let rctx' = RTypectx.new_to_right rctx xret in
          let tau = infer_eff opctx rctx' letbody in
          (* Apply Exist instead of Abduce *)
          let tau_result = exist_quantify_monad rctx xret tau in
          let eff_bound = bind_effects tau_x.eff tau_result.eff in
          { ret = tau_result.ret; eff = eff_bound })
  | _ -> _failatwith __FILE__ __LINE__ "die"

(** Helper function to infer operator types *)
and infer_op opctx rctx (arg_rtys, ret_eff_ty) (op : Op.t typed) :
    string rtyped list * monad =
  let rec multi_app rxs arg_rtys hty =
    match arg_rtys with
    | [] -> (List.rev rxs, hty)
    | arg_rty :: arg_rtys -> (
        let rty = hty_force_rty hty in
        let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
        match arr with
        | ArrArr rty -> _failatwith __FILE__ __LINE__ "Higher order operator"
        | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
        | NormalArr rx ->
            let rx = { rx with rty = union_rty (rx.rty, arg_rty) } in
            multi_app (rx :: rxs) arg_rtys rethty)
  in
  let rxs, hty = multi_app [] arg_rtys (Rty (ROpTypectx.get_ty opctx op.x)) in
  ( rxs,
    union_effty_monad (RTypectx.new_to_rights rctx rxs) ret_eff_ty
    @@
    match op.x with
    | Op.BuiltinOp _ -> of_rty_monad @@ hty_force_rty hty
    | Op.EffOp _ -> hty_force_monad hty
    | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die" )

(** Helper function to apply existential quantification (replacing Abduce) *)
and exist_quantify_monad rctx xret tau =
  existential_monad xret tau

(** Helper function to bind effects *)
and bind_effects eff1 eff2 =
  Eff.Seq (eff1, eff2)

(** Helper functions for monad operations *)
and existential_monad { rx = cx; rty } =
  match rty with
  | ArrRty _ -> Fun.id
  | BaseRty { cty } -> (
      function
      | { ret; eff } ->
          assert (not @@ List.exists (String.equal cx) @@ fv_rty ret.rty);
          { ret; eff = Eff.Bind ((cx #::: cty), eff) })

and multi_existential_monad rxs = List.fold_right existential_monad rxs

and of_rty_monad rty = { ret = "ret" #:: rty; eff = Eff.Atom Eff.Id }

and hty_force_monad = function
  | Monad monad -> monad
  | _ -> _failatwith __FILE__ __LINE__ "hty_force_monad"

and union_effty_monad rctx monad1 monad2 =
  let ret_rty = union_rty (monad1.ret.rty, monad2.ret.rty) in
  let ret = { rx = monad1.ret.rx; rty = ret_rty } in
  let eff = Eff.Choice (monad1.eff, monad2.eff) in
  { ret; eff }
