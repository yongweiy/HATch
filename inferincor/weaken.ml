open Sugar
open Language
open TypedCoreEff
open Rty
open Typing
open Aux

let ( let* ) x f = Choice.bind f x
let ( let^ ) x f = Choice.fmap f x
let ( let+ ) x f = Choice.map f x

let rec weaken_pure opctx rctx (rty_in : rty) (value : value typed) : rty =
  match value.x with
  | VConst c ->
      let rty = mk_rty_var_eq_c value.ty c in
      if Subtyping.is_bot_rty rctx @@ inter_rty (rty_in, rty) then
        _failatwith __FILE__ __LINE__ "Weakening Failure"
      else rty
  | VVar x ->
      let _ = rty_force_cty rty_in in
      let rty = inter_rty (rty_in, mk_rty_var_eq_var x #: value.ty) in
      if Subtyping.is_bot_rty rctx rty then
        _failatwith __FILE__ __LINE__ "Weakening Failure"
      else rty
  | VLam { lamarg; lambody } -> (
      let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty_in in
      match arr with
      | ArrArr rty -> _failatwith __FILE__ __LINE__ "Higher order function"
      | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
      | NormalArr rx ->
          assert (rx.rx = lamarg.x);
          let rctx = RTypectx.new_to_right rctx rx in
          let effty_in = hty_force_tmonad rethty in
          let effty_out = weaken_eff opctx rctx effty_in lambody in
          let rty = ArrRty { arr = NormalArr rx; rethty = TMonad effty_out } in
          if Subtyping.is_bot_rty rctx rty then
            _failatwith __FILE__ __LINE__ "Weakening Failure"
          else rty)
  | VFix _ -> _failatwith __FILE__ __LINE__ "unimp"
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

and weaken_op opctx rctx (arg_rtys, ret_eff_ty) (op : Op.t typed) :
    string rtyped list * tmonad =
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
            let rx = { rx with rty = inter_rty (rx.rty, arg_rty) } in
            multi_app (rx :: rxs) arg_rtys rethty)
  in
  let rxs, hty = multi_app [] arg_rtys (Rty (ROpTypectx.get_ty opctx op.x)) in
  ( rxs,
    union_effty (RTypectx.new_to_rights rctx rxs) ret_eff_ty
    @@
    match op.x with
    | Op.BuiltinOp _ -> of_rty @@ hty_force_rty hty
    | Op.EffOp _ -> hty_force_tmonad hty
    | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die" )

and weaken_eff opctx rctx (eff_ty : tmonad) (expr : comp typed) : tmonad =
  let { ret; trans } = eff_ty in
  let[@warning "-8"] (PreAndPost (pre, post)) = trans in
  let bind ?(locals = []) (x, { ret = xret; trans = xtrans }) body =
    let xret = under_to_over_rtyped { xret with rx = x } in
    let[@warning "-8"] (PreToPost xtrans) =
      subst_trans (xret.rx, AVar x) xtrans
    in
    Srt.display xtrans;
    let rctx = RTypectx.new_to_right rctx xret in
    let eff_ty =
      weaken_eff opctx rctx
        { ret; trans = PreAndPost (Srt.mk_ran ~rctx xtrans, post) }
        body
    in
    multi_existential locals @@ existential xret eff_ty
  in
  match expr.x with
  | CVal v ->
      let retrty = weaken_pure opctx rctx ret.rty v #: expr.ty in
      let ret = { ret with rty = retrty } in
      let rctx = RTypectx.new_to_right rctx ret in
      let trans = Srt.restrict_domain ~rctx Srt.mk_ident pre in
      Srt.display trans;
      { ret; trans = PreToPost trans }
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CApp { appf; apparg } -> _failatwith __FILE__ __LINE__ "die"
      | CAppOp { op; appopargs } ->
          let arg_rtys =
            List.map
              (fun arg -> weaken_pure opctx rctx (refine_to_ceil arg.ty) arg)
              appopargs
          in
          let locals, x_eff_ty =
            weaken_op opctx rctx (arg_rtys, of_ty_pre rhs.ty pre) op
          in
          bind ~locals (lhs.x, x_eff_ty) letbody
      | _ ->
          let x_eff_ty = weaken_eff opctx rctx (of_ty_pre rhs.ty pre) rhs in
          bind (lhs.x, x_eff_ty) letbody)
  | _ -> _failatwith __FILE__ __LINE__ "die"
