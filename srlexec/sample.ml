(** sample literal traces from a regex, useful for under-approximated
    reasoning of pre-condition regex.  The sampling algorithm is
    similar to BFS on the automaton constructed via regex derivative
    while the search does not have a goal and is bounded by a given
    number. *)

open Zzdatatype.Datatype
open Language

(* open Syntax *)
open Sugar
open Rty
open Literal
open Deriv

let ( let* ) x f = C.bind f x
let ( let+ ) x f = C.map f x
let def_tr_len_bound = 2

let uncons_regex ~rctx ~gvars r =
  let* l = next_literal ~rctx ~gvars r in
  let* () = Choice.guard @@ not @@ Literal.is_bot_literal ~rctx ~gvars l in
  Choice.return (l, fst @@ symb_deriv_over_lit ~rctx ~gvars r l)
(* |> filter (fun (_, r) -> not @@ SRL.is_empty r) *)

let sample_regex ~rctx ~gvars ?(bound = def_tr_len_bound) r =
  let rec loop bound tr_rev regex =
    let open Choice in
    if bound = 0 then return tr_rev
    else
      next_literal ~rctx ~gvars regex >>= fun lit ->
      match symb_deriv_over_lit ~rctx ~gvars regex lit with
      | EmptyA, _ -> fail
      | regex', _ -> loop (bound - 1) (lit :: tr_rev) regex'
  in
  loop bound [] r

let sample_regex' ~rctx ~gvars ?(bound = def_tr_len_bound) r =
  let open Choice in
  let lifted_deriv tr_r_pairs =
    (* Pp.printf "lifted_deriv:\n"; *)
    tr_r_pairs >>= fun (tr, r) ->
    (* print_trace tr; *)
    next_literal ~rctx ~gvars r >>= fun lit ->
    match symb_deriv_over_lit ~rctx ~gvars r lit with
    | EmptyA, _ -> fail
    | r', _ -> return (lit :: tr, r')
  in
  let rec loop bound res =
    Pp.printf "loop: %d\n" bound;
    Choice.iter res (fun (tr, r) ->
        print_trace tr;
        Pp.printf "%s\n" @@ Rty.layout_regex r;
        true);
    if bound = 0 then res else loop (bound - 1) (lifted_deriv res)
  in
  loop bound (return ([], r)) |> Choice.map fst
