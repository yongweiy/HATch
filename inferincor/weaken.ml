open Sugar
open Core.Option.Let_syntax
open Language
open TypedCoreEff
open Rty
open Typing

(** Interleaved type weakening and inference following updated rules *)

let ( let* ) x f = Choice.bind f x
let ( let^ ) x f = Choice.fmap f x
let ( let+ ) x f = Choice.map f x

(** Type synthesis for values following Syn* rules *)
let rec infer_pure opctx rctx (value : value typed) : rty =
  match value.x with
  | VConst c ->
      (* SynConst rule: Γ ⊢ c ↑ {b | ν = c} *)
      mk_rty_var_eq_c value.ty c
  | VVar x -> (
      (* SynVar and SynVarFun rules *)
      match RTypectx.get_ty_opt rctx x with
      | Some rty -> (
          match rty with
          | BaseRty _ -> mk_rty_var_eq_var x #: value.ty
          | ArrRty _ -> rty)
      | None -> mk_rty_var_eq_var x #: value.ty)
  | VLam { lamarg; lambody } ->
      (* SynFun rule modified: takes input type from context *)
      let rx = { rx = lamarg.x; rty = mk_ceil_pure lamarg.ty } in
      let rctx' = RTypectx.new_to_right rctx rx in
      let tau = infer_eff opctx rctx' lambody in
      ArrRty { arr = NormalArr rx; rethty = Monad tau }
  | VFix _ -> _failatwith __FILE__ __LINE__ "unimp"
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

(** Type synthesis for computations following Syn* rules *)
and infer_eff opctx rctx (expr : comp typed) : monad =
  match expr.x with
  | CVal v ->
      (* SynLift rule: Γ ⊢ v ↑ t, FT[r] = ret v ⟹ Γ ⊢ v ↑ M(t, FT[r]) *)
      let t = infer_pure opctx rctx v #: expr.ty in
      let ret = { rx = "ret"; rty = t } in
      { ret; eff = Eff.Atom Eff.Id }
  | CLetE { lhs; rhs; letbody } -> (
      (* SynLet rule with Abduce replaced by existential quantification *)
      match rhs.x with
      | CAppOp { op; appopargs } ->
          let arg_rtys = List.map (fun arg -> infer_pure opctx rctx arg) appopargs in
          let locals, x_eff_ty = infer_op opctx rctx (arg_rtys, mk_ceil_eff rhs.ty) op in
          let xret = { rx = lhs.x; rty = x_eff_ty.ret.rty } in
          let rctx' = RTypectx.new_to_right rctx xret in
          let tau = infer_eff opctx rctx' letbody in
          let tau_result = existential xret tau in
          let eff_bound = Eff.Seq (x_eff_ty.eff, tau_result.eff) in
          multi_existential locals { ret = tau_result.ret; eff = eff_bound }
      | _ ->
          let tau_x = infer_eff opctx rctx rhs in
          let xret = { rx = lhs.x; rty = tau_x.ret.rty } in
          let rctx' = RTypectx.new_to_right rctx xret in
          let tau = infer_eff opctx rctx' letbody in
          let tau_result = existential xret tau in
          let eff_bound = Eff.Seq (tau_x.eff, tau_result.eff) in
          { ret = tau_result.ret; eff = eff_bound })
  | _ -> _failatwith __FILE__ __LINE__ "die"

(** Type weakening for values following WK* rules *)
and weaken_pure opctx rctx (rty_in : rty) (value : value typed) : rty =
  match value.x with
  | VLam { lamarg; lambody } -> (
      (* Handle lambda weakening with input type (updated SynFun rule) *)
      let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty_in in
      match arr with
      | ArrArr _ -> _failatwith __FILE__ __LINE__ "Higher order function"
      | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
      | NormalArr rx ->
          (* SynFun rule: Γ,x:t_x ⊢ τ₁ ↓ e ↑ τ₂ ⟹ Γ ⊢ x:t_x→τ₁ ↓ λx.e ↑ x:t_x→τ₂ *)
          assert (rx.rx = lamarg.x);
          let rctx' = RTypectx.new_to_right rctx rx in
          let effty_in = hty_force_monad rethty in
          let effty_out = weaken_eff opctx rctx' effty_in lambody in
          let result_rty = ArrRty { arr = NormalArr rx; rethty = Monad effty_out } in
          if Subtyping.is_bot_rty rctx result_rty then
            _failatwith __FILE__ __LINE__ "Weakening Failure"
          else result_rty)
  | _ ->
      (* WKPure rule: Γ ⊢ v ↑ t, Γ ⊢ t₁ ∨ t = t₂ ⟹ Γ ⊢ t₁ ↓ v ↑ t₂ *)
      let inferred_rty = infer_pure opctx rctx value in
      let result_rty = union_rty (rty_in, inferred_rty) in
      if Subtyping.is_bot_rty rctx result_rty then
        _failatwith __FILE__ __LINE__ "Weakening Failure"
      else result_rty

(** Type weakening for computations following WK* rules *)
and weaken_eff opctx rctx (eff_ty_in : monad) (expr : comp typed) : monad =
  (* WKEff rule: Γ ⊢ e ↑ τ, Γ ⊢ τ₁ ∨ τ = τ₂ ⟹ Γ ⊢ τ₁ ↓ e ↑ τ₂ *)
  let inferred_eff = infer_eff opctx rctx expr in
  let result_eff = union_effty rctx eff_ty_in inferred_eff in
  if Subtyping.is_bot_rty rctx result_eff.ret.rty then
    _failatwith __FILE__ __LINE__ "Weakening Failure"
  else result_eff


(** Operator inference *)
and infer_op opctx rctx (arg_rtys, ret_eff_ty) (op : Op.t typed) :
    string rtyped list * monad =
  let rec multi_app rxs arg_rtys hty =
    match arg_rtys with
    | [] -> (List.rev rxs, hty)
    | arg_rty :: arg_rtys -> (
        let rty = hty_force_rty hty in
        let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
        match arr with
        | ArrArr _ -> _failatwith __FILE__ __LINE__ "Higher order operator"
        | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
        | NormalArr rx ->
            let rx = { rx with rty = union_rty (rx.rty, arg_rty) } in
            multi_app (rx :: rxs) arg_rtys rethty)
  in
  let rxs, hty = multi_app [] arg_rtys (Rty (ROpTypectx.get_ty opctx op.x)) in
  ( rxs,
    union_effty (RTypectx.new_to_rights rctx rxs) ret_eff_ty
    @@
    match op.x with
    | Op.BuiltinOp _ -> of_rty @@ hty_force_rty hty
    | Op.EffOp _ -> hty_force_monad hty
    | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die" )

(** Helper functions *)
and hty_force_rty = function
  | Rty rty -> rty
  | _ -> _failatwith __FILE__ __LINE__ "hty_force_rty"

and hty_force_monad = function
  | Monad monad -> monad
  | _ -> _failatwith __FILE__ __LINE__ "hty_force_monad"

and multi_existential rxs = List.fold_right existential rxs
