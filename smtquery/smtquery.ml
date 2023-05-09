exception FailWithModel of string * Z3.Model.model

let _failwithmodel file line msg model =
  raise (FailWithModel (Printf.sprintf "[%s:%i] %s" file line msg, model))

let ctx =
  Z3.mk_context [ ("model", "true"); ("proof", "false"); ("timeout", "99999") ]

exception SMTTIMEOUT

let handle_check_res query_action =
  let open Check in
  let time_t, res = Sugar.clock query_action in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>Solving time: %.2f@}\n" time_t
  in
  match res with
  | SmtUnsat -> None
  | SmtSat model ->
      ( Env.show_debug_stat @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 100 @@ Z3.Model.to_string model );
      Some model
  | Timeout -> raise SMTTIMEOUT

let _check pre q =
  handle_check_res (fun () -> Check.smt_neg_and_solve ctx pre q)

let check_with_pre pres vc = _check pres vc

let check_implies_with_pre pres a b =
  _check pres Language.Rty.P.(Implies (a, b))

let check vc = check_with_pre [] vc
let check_implies a b = check_implies_with_pre [] a b

let check_inclusion (r1, r2) =
  handle_check_res (fun () -> Check.inclusion_query ctx r1 r2)

open Language.NRegex

let test0 () =
  let r1 = Epslion in
  (* let r1 = Minterm ("Put", 3) in *)
  let r2 = Minterm ("Put", 3) in
  match check_inclusion (r2, r1) with
  | None ->
      let () = Printf.printf "true" in
      ()
  | _ ->
      let () = Printf.printf "false" in
      ()
