open Zzdatatype.Datatype
open Language
open Syntax
open Sugar
open Rty

let rec is_nullable = function
  | EmptyA -> false
  | EpsilonA -> true
  | AnyA -> false
  | EventA (GuardEvent _) -> false
  | EventA (EffEvent _) -> false
  | LorA (r, s) -> is_nullable r || is_nullable s
  | LandA (r, s) -> is_nullable r && is_nullable s
  | SeqA (r, s) -> is_nullable r && is_nullable s
  | StarA _ -> true
  | ComplementA r -> not (is_nullable r)
  | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "is_nullable: SetMinusA"

(** TODO: as its computation is expensive and the same (sub-)regex may
    appear multiple times, shall we memoize it in some way? *)
let rec next_literal ?(constr = P.mk_true) = function
  | EmptyA | EpsilonA -> Choice.fail
  | AnyA -> Choice.return @@ Literal.mk_true
  | EventA sev -> Choice.return @@ Literal.of_sevent sev
  | LorA (r, s) ->
      Literal.join ~constr (next_literal ~constr r) (next_literal ~constr s)
  | LandA (r, s) ->
      Choice.product (next_literal ~constr r) (next_literal ~constr s)
      |> Choice.map (fun (l1, l2) -> Literal.mk_and l1 l2)
  | SeqA (r, s) when is_nullable r ->
      Literal.join ~constr (next_literal ~constr r) (next_literal ~constr s)
  | SeqA (r, s) -> next_literal ~constr r
  | StarA r -> next_literal ~constr r
  (* TODO: can we do better? pruning? ordering? *)
  | ComplementA r ->
      let lits = next_literal ~constr r in
      Choice.(lits ++ delay (fun () -> return @@ Literal.neg_literals lits))
  | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "next_literal: SetMinusA"

let prop_entail_prop ~constr phi1 phi2 =
  Smtquery.check_bool @@ smart_implies (smart_and [ constr; phi1 ]) phi2

let lit_entails_sev ~constr lit sev =
  let open Literal in
  (* TODO: guard event *)
  let ev =
    match sev with
    | EffEvent ev -> ev
    | GuardEvent _ ->
        _failatwith __FILE__ __LINE__ "lit_entails_sev: GuardEvent"
  in
  match lit with
  | { events = [ ev' ]; op_filter = `Whitelist [] }
    when ev.op = ev'.op && prop_entail_prop ~constr ev'.phi ev.phi ->
      true
  | { events = []; op_filter = `Whitelist [ op ] } when ev.op = op -> true
  | { events = []; op_filter = `Blacklist ops } when not (List.mem ev.op ops) ->
      true
  | _ -> false

let mk_orA r s =
  if r = s then r
  else if r = EmptyA then s
  else if s = EmptyA then r
  else LorA (r, s)

let mk_andA r s =
  if r = s then r
  else if r = EmptyA then EmptyA
  else if s = EmptyA then EmptyA
  else LandA (r, s)

let mk_seqA r s = if r = EpsilonA then s else SeqA (r, s)

let symb_deriv_over_lit ?(constr = P.mk_true) r lit =
  let rec aux = function
    | EmptyA | EpsilonA -> EmptyA
    | AnyA -> AnyA
    | EventA sev when lit_entails_sev ~constr lit sev -> EpsilonA
    | EventA _ -> EmptyA
    | LorA (r, s) -> mk_orA (aux r) (aux s)
    | LandA (r, s) -> mk_andA (aux r) (aux s)
    | SeqA (r, s) when is_nullable r -> mk_orA (mk_seqA (aux r) s) (aux s)
    | SeqA (r, s) -> mk_seqA (aux r) s
    | StarA r -> mk_seqA (aux r) (StarA r)
    | ComplementA r -> ComplementA (aux r)
    | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "symb_deriv: SetMinusA"
  in
  aux r

let symb_deriv ?(constr = P.mk_true) lit r =
  let open Choice in
  let open Literal in
  (* TODO: as only disjoint subsets of `lit` are of our interest, we
     shall specialize/optimize `left_join` for this purpose *)
  let time_t, lits =
    clock (fun () -> left_join ~constr (return lit) (next_literal ~constr r))
  in
  (* Pp.printf "left_join time: %f\n" time_t; *)
  lits
  |> bind (fun l ->
         let time_t, r_choice =
           clock (fun () -> return @@ symb_deriv_over_lit ~constr r l)
         in
         (* Pp.printf "symb_deriv_over_lit time: %f\n" time_t; *)
         r_choice >>= fun r ->
         guard (not @@ SRL.is_empty r) >>= fun () -> return r)

let symb_quot ?(constr = P.mk_true) trace regex =
  List.fold_left
    (fun r_choice lit -> Choice.(r_choice >>= symb_deriv ~constr lit))
    (Choice.return regex) trace

let symb_match ?(constr = P.mk_true) trace regex =
  symb_quot ~constr trace regex |> Choice.map is_nullable |> Choice.forall

type ghost_constr = (prop * prop) list
(** Say `unzip ghost_constr = (phi, psi)` where
    `phi`(sev) and `psi`(regex) are both conjunction of constraints.
    /backward matching/ produces `ghost_constr` to be interprets as
    pre-condition `forall x v. phi(x, v) => exists a. psi(x, a)`
    where `x` is the distinct local variables shared by sev and regex,
    `v` is global variables whose constraints are omitted here, and
    `a` is the ghost variables introduced by regex.
    /forward maching/ consumes `ghost_constr` as post-condition
    post-condition `forall v a. exists x. phi(x, v) /\ psi(x, a)`.
*)

type ghost_info = (string * ghost_constr) list
type mode = Fwd | Bwd of string list

let rec deriv r sev =
  match r with
  | EmptyA -> EmptyA
  | EpsilonA -> EmptyA
  | AnyA -> EpsilonA
  | EventA (GuardEvent _) ->
      _failatwith __FILE__ __LINE__ "deriv: GuardEvent UNIMP"
  | EventA (EffEvent { op; vs; v; phi }) when is_effevent_with_op op sev -> (
      let vs = List.map (fun typed -> typed.x) (v :: vs) in
      let fvs = fv_prop phi in
      let fvs = List.filter (fun v0 -> not (List.mem v0 vs)) fvs in
      _assert __FILE__ __LINE__ "deriv: free variable UNIMP"
      @@ List.is_empty fvs;
      let[@warning "-8"] (EffEvent effev) = sev in
      (* TODO: assert vs and v of the current event align *)
      match Smtquery.check (Implies (effev.phi, phi)) with
      | None -> EpsilonA
      | Some _ -> EmptyA)
  | EventA (EffEvent { op; vs; v; phi }) ->
      _assert __FILE__ __LINE__ "deriv: GuardEvent UNIMP" @@ is_effevent sev;
      EmptyA
  | LorA (r, s) -> LorA (deriv r sev, deriv s sev)
  | LandA (r, s) -> LandA (deriv r sev, deriv s sev)
  | SeqA (r, s) ->
      if is_nullable r then LorA (SeqA (deriv r sev, s), deriv s sev)
      else SeqA (deriv r sev, s)
  | StarA r -> SeqA (deriv r sev, StarA r)
  | ComplementA r -> ComplementA (deriv r sev)
  | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "deriv: SetMinusA"

let fwd_match sev_list regex =
  List.fold_left deriv regex sev_list |> is_nullable

let bwd_match sev_list regex =
  List.rev sev_list |> List.fold_left deriv regex |> is_nullable
