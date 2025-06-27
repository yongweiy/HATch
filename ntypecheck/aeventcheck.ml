open Language
open Sugar
open Qualifiercheck
open RtyRaw
open RtyRaw.Sft.LAlg

let check_pred opctx ctx { events; op_pred } =
  {
    events = List.map (Secheck.check_eff_event opctx ctx) events;
    op_pred =
      (match op_pred with
      | Whitelist _ -> op_pred
      | Blacklist (phi, ops) ->
          Blacklist (type_check_qualifier opctx ctx phi, ops));
  }

let check_ev opctx ctx { op; args; ret } =
  let orty = Aux.infer_op opctx (Op.EffOp op) in
  let argsty, retnty = Nt.destruct_arr_tp orty in
  let args =
    List.map
      (fun (arg, ty) -> type_check_lit opctx ctx (arg.x, ty))
      (_safe_combine __FILE__ __LINE__ args argsty)
  in
  let ret = type_check_lit opctx ctx (ret.x, retnty) in
  { op; args; ret }

let check_func opctx ctx = function
  | IdentityF -> IdentityF
  | EventF ev -> EventF (check_ev opctx ctx ev)
