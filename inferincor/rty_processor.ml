open Sugar
open Language
open Rty

(** Process refinement types to replace Call effects with actual operator effects *)

let rec process_eff opctx = function
  | Eff.Atom (Call { op; args; ret }) ->
      (* Look up the operator in opctx and get its effect *)
      (match ROpTypectx.get_ty_opt opctx op with
       | Some op_rty ->
           (* Extract effect from operator type - similar to infer_op logic *)
           let op_hty = Rty op_rty in
           (match op_hty with
            | Monad { eff; _ } -> eff
            | Rty _ -> Eff.Atom Eff.Id  (* Pure operator *)
            | _ -> Eff.Atom (Call { op; args; ret }))  (* Fallback *)
       | None -> Eff.Atom (Call { op; args; ret }))  (* Operator not found, keep as is *)
  | Eff.Atom atom -> Eff.Atom atom
  | Eff.Reach eff -> Eff.Reach (process_eff opctx eff)
  | Eff.Bind (ctyped, eff) -> Eff.Bind (ctyped, process_eff opctx eff)
  | Eff.Guard p -> Eff.Guard p
  | Eff.Seq (eff1, eff2) -> Eff.Seq (process_eff opctx eff1, process_eff opctx eff2)
  | Eff.Choice (eff1, eff2) -> Eff.Choice (process_eff opctx eff1, process_eff opctx eff2)

let rec process_hty opctx = function
  | Rty rty -> Rty (process_rty opctx rty)
  | Monad { ret; eff } -> 
      Monad { ret = { ret with rty = process_rty opctx ret.rty }; 
              eff = process_eff opctx eff }
  | Htriple { pre; resrty; post } ->
      Htriple { pre; resrty = process_rty opctx resrty; post }
  | Inter (hty1, hty2) -> 
      Inter (process_hty opctx hty1, process_hty opctx hty2)

and process_rty opctx = function
  | BaseRty { cty } -> BaseRty { cty }
  | ArrRty { arr; rethty } ->
      ArrRty { arr = process_arr opctx arr; rethty = process_hty opctx rethty }

and process_arr opctx = function
  | NormalArr { rx; rty } -> NormalArr { rx; rty = process_rty opctx rty }
  | GhostArr x -> GhostArr x
  | ArrArr rty -> ArrArr (process_rty opctx rty)

(** Main entry point to process an rty and replace Call effects *)
let process_input_rty opctx rty = process_rty opctx rty
