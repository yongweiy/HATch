open Language
open Rty
open Sugar
open Aux

let close_to_cty (x : dep_quantifer) { v; phi } =
  { v; phi = close_to_prop x phi }

let _check_quantifer_alternation file line (x : dep_quantifer) ou =
  match (x, ou) with
  | SigmaTy _, Over -> _failatwith file line "quantifer_alternation"
  | PiTy _, Under -> _failatwith file line "quantifer_alternation"
  | _ -> ()

let rec close_to_pty (x : dep_quantifer) = function
  | BasePty { ou; cty } ->
      let () = _check_quantifer_alternation __FILE__ __LINE__ x ou in
      BasePty { ou; cty = close_to_cty x cty }
  | TuplePty tys -> TuplePty (List.map (close_to_pty x) tys)
  | ArrPty { rarg; retrty } ->
      if List.mem (dep_quantifer_get_id x) (fv_pty rarg.pty) then
        _failatwith __FILE__ __LINE__ "quantifer_alternation"
      else ArrPty { rarg; retrty = close_to_rty x retrty }

and close_to_rty (x : dep_quantifer) rty =
  match rty with
  | Pty pty -> Pty (close_to_pty x pty)
  | Regty _ | Sigmaty _ -> Sigmaty { localx = dep_quantifer_to_typed x; rty }

(* and close_to_sevent x sevent = *)
(*   match sevent with *)
(*   | RetEvent pty -> RetEvent (close_to_pty x pty) *)
(*   | EffEvent { op; vs; phi } -> EffEvent { op; vs; phi = close_to_prop x phi } *)

(* and close_to_regex x regex = *)
(*   match x with *)
(*   | SigmaTy localx -> ExistsA { localx; regex } *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

let exists_typed x rty =
  match typed_to_dep_quantifer_opt x with
  | Some x -> close_to_rty x rty
  | None -> Sigmaty { localx = x; rty }

let exists_ptyped x rty =
  let x = ptyped_to_dep_quantifer x in
  close_to_rty x rty

(* let exists_typed_to_cty x rty = *)
(*   let x = typed_to_dep_quantifer x in *)
(*   close_to_cty x rty *)

let exists_ptyped_to_cty x rty =
  let x = ptyped_to_dep_quantifer x in
  close_to_cty x rty
