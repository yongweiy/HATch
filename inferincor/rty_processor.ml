open Sugar
open Language
open Rty

(* Helper functions mirroring those in weaken.ml *)
let hty_force_rty = function
  | Rty rty -> rty
  | _ -> _failatwith __FILE__ __LINE__ "hty_force_rty in rty_processor"

let hty_force_monad = function
  | Monad monad -> monad
  | _ -> _failatwith __FILE__ __LINE__ "hty_force_monad in rty_processor"

(** Shared logic for extracting parameters and effects from operator types *)
let extract_op_params_and_effect opctx op args =
  match ROpTypectx.get_ty_opt opctx (EffOp op) with
  | Some op_rty ->
      let rec extract_params_and_effect acc_rxs hty remaining_args =
        match remaining_args with
        | [] -> (
            (* No more arguments, extract the final effect *)
            match hty with
            | Monad { ret = final_ret; eff } ->
                (List.rev acc_rxs, final_ret, eff)
            | Rty _ ->
                ( List.rev acc_rxs,
                  { rx = "ret"; rty = hty_force_rty hty },
                  Eff.Atom Eff.Id )
            | _ -> 
                _failatwith __FILE__ __LINE__ 
                  "extract_op_params_and_effect: unsupported hty type")
        | arg :: remaining_args -> (
            (* More arguments to process, destructure the function type *)
            let rty = hty_force_rty hty in
            let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
            match arr with
            | NormalArr rx ->
                extract_params_and_effect (rx :: acc_rxs) rethty remaining_args
            | _ -> 
                _failatwith __FILE__ __LINE__ 
                  "extract_op_params_and_effect: unsupported array type")
      in
      extract_params_and_effect [] (Rty op_rty) args
  | None -> 
      _failatwith __FILE__ __LINE__ 
        "extract_op_params_and_effect: operator not found in opctx"

(** Process refinement types to replace Call effects with actual operator effects *)

let rec process_eff opctx = function
  | Eff.Atom (Call { op; args; ret }) -> (
      (* Use shared extraction logic *)
      let (rxs, final_ret, eff) = extract_op_params_and_effect opctx op args in
      (* TODO: assumed that [rxs] and [final_ret] has top
         qualifier *)
      let substitutions =
        (final_ret.rx, ret.x)
        :: List.map2 (fun rx arg -> (rx.rx, arg.x)) rxs args
      in
      List.fold_left
        (fun eff_acc (var, lit_val) -> subst_eff (var, lit_val) eff_acc)
        eff substitutions)
  | Eff.Atom atom -> Eff.Atom atom
  | Eff.Constrain (eff1, eff2) -> Eff.Constrain (process_eff opctx eff1, process_eff opctx eff2)
  | Eff.Bind (ctyped, eff) -> Eff.Bind (ctyped, process_eff opctx eff)
  | Eff.Guard p -> Eff.Guard p
  | Eff.Seq (eff1, eff2) ->
      Eff.Seq (process_eff opctx eff1, process_eff opctx eff2)
  | Eff.Choice (eff1, eff2) ->
      Eff.Choice (process_eff opctx eff1, process_eff opctx eff2)

let rec process_hty opctx = function
  | Rty rty -> Rty (process_rty opctx rty)
  | Monad { ret; eff } ->
      Monad
        {
          ret = { ret with rty = process_rty opctx ret.rty };
          eff = process_eff opctx eff;
        }
  | Htriple { pre; resrty; post } ->
      Htriple { pre; resrty = process_rty opctx resrty; post }
  | Inter (hty1, hty2) -> Inter (process_hty opctx hty1, process_hty opctx hty2)

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
