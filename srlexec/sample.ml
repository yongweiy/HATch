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

let def_tr_len_bound = 2

let sample_regex ?(constr = P.mk_true) ?(bound = def_tr_len_bound) r =
  let rec loop bound tr_rev regex =
    let open Choice in
    if bound = 0 then return tr_rev
    else
      next_literal ~constr regex >>= fun lit ->
      match symb_deriv_over_lit ~constr regex lit with
      | EmptyA -> fail
      | regex' -> loop (bound - 1) (lit :: tr_rev) regex'
  in
  loop bound [] r

let sample_regex' ?(constr = P.mk_true) ?(bound = def_tr_len_bound) r =
  let open Choice in
  let lifted_deriv tr_r_pairs =
    (* Pp.printf "lifted_deriv:\n"; *)
    tr_r_pairs >>= fun (tr, r) ->
    (* print_trace tr; *)
    next_literal ~constr r >>= fun lit ->
    match symb_deriv_over_lit ~constr r lit with
    | EmptyA -> fail
    | r' -> return (lit :: tr, r')
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
