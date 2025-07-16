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
  | CLetE { lhs; rhs; letbody } ->
      let locals, monadx = match rhs.x with
        | CAppOp { op; appopargs } ->
            let arg_rtys =
              List.map (fun arg -> infer_pure opctx rctx arg) appopargs
            in
            infer_op opctx rctx lhs op arg_rtys
        | _ -> 
            ([], infer_eff opctx rctx rhs)
      in
      let rx = { rx = lhs.x; rty = monadx.ret.rty } in
      let rctx' = RTypectx.new_to_right (RTypectx.new_to_rights rctx locals) rx in
      let monad = multi_externalize locals @@ externalize rx @@ infer_eff opctx rctx' letbody in
      {
        monad with
        eff = multi_existential_eff locals @@ eff_bind monadx (rx.rx, monad.eff);
      }
  | CMatch { matched; match_cases } ->
    (* SynMatch rule: infer type for each case and join them together *)
    let _matched_rty = infer_pure opctx rctx matched in
    let case_monads = List.map (fun (_pattern, case_expr) ->
      (* TODO: properly handle pattern bindings in context *)
      infer_eff opctx rctx case_expr
    ) match_cases in
    (* Join all case types together *)
    match case_monads with
    | [] -> _failatwith __FILE__ __LINE__ "Empty match cases"
    | first :: rest ->
        List.fold_left (fun acc_monad case_monad ->
          match union_effty rctx acc_monad case_monad with
          | Some unified -> unified
          | None -> _failatwith __FILE__ __LINE__ "Cannot unify match case types"
        ) first rest
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
          let effty_in = hty_to_monad __FILE__ __LINE__ rethty in
          let effty_out = weaken_eff opctx rctx' effty_in lambody in
          let result_rty =
            ArrRty { arr = NormalArr rx; rethty = Monad effty_out }
          in
          if Subtyping.is_bot_rty rctx result_rty then
            _failatwith __FILE__ __LINE__ "Weakening Failure"
          else result_rty)
  | _ -> (
      (* WKPure rule: Γ ⊢ v ↑ t, Γ ⊢ t₁ ∨ t = t₂ ⟹ Γ ⊢ t₁ ↓ v ↑ t₂ *)
      let inferred_rty = infer_pure opctx rctx value in
      match union_rty (rty_in, inferred_rty) with
      | Some result_rty ->
          if Subtyping.is_bot_rty rctx result_rty then
            _failatwith __FILE__ __LINE__ "Weakening Failure"
          else result_rty
      | None -> _failatwith __FILE__ __LINE__ "Weakening Failure")

(** Type weakening for computations following WK* rules *)
and weaken_eff opctx rctx (eff_ty_in : monad) (expr : comp typed) : monad =
  (* WKEff rule: Γ ⊢ e ↑ τ, Γ ⊢ τ₁ ∨ τ = τ₂ ⟹ Γ ⊢ τ₁ ↓ e ↑ τ₂ *)
  let inferred_eff = infer_eff opctx rctx expr in
  match union_effty rctx eff_ty_in inferred_eff with
  | Some result_eff ->
      if Subtyping.is_bot_rty rctx result_eff.ret.rty then
        _failatwith __FILE__ __LINE__ "Weakening Failure"
      else result_eff
  | None -> _failatwith __FILE__ __LINE__ "Weakening Failure"

(** Operator inference *)
and infer_op opctx rctx lhs (op : Op.t typed) arg_rtys :
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
            let rx =
              match union_rty (rx.rty, arg_rty) with
              | Some rty -> { rx = rx.rx ^ "_" ^ lhs.x; rty }
              | None ->
                  _failatwith __FILE__ __LINE__ "union_rty failed in infer_op"
            in
            multi_app (rx :: rxs) arg_rtys rethty)
  in
  let rxs, hty = multi_app [] arg_rtys (Rty (ROpTypectx.get_ty opctx op.x)) in
  let monad =
    match op.x with
    | Op.BuiltinOp _ -> of_rty @@ hty_to_rty __FILE__ __LINE__ hty
    | Op.EffOp _ -> hty_to_monad __FILE__ __LINE__ hty
    | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
  in
  (rxs, monad)
