open Zzdatatype.Datatype
open Language
open Sugar
open Rty
open Literal
module C = Choice

let ( let* ) x f = C.bind f x
let ( let+ ) x f = C.map f x

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
  | SetMinusA (r, s) -> is_nullable r && not (is_nullable s)

(** TODO: as its computation is expensive and the same (sub-)regex may
    appear multiple times, shall we memoize it in some way? *)
let rec next_literal ~rctx ~gvars ?(ghosts = []) = function
  | EmptyA | EpsilonA -> Choice.fail
  | AnyA -> Choice.return @@ Literal.mk_true
  | EventA sev -> Choice.return @@ Literal.of_sevent ~ghosts sev
  | LorA (r, s) ->
      Literal.join ~rctx ~gvars
        (next_literal ~rctx ~gvars ~ghosts r)
        (next_literal ~rctx ~gvars ~ghosts s)
  | LandA (r, s) ->
      Choice.product
        (next_literal ~rctx ~gvars ~ghosts r)
        (next_literal ~rctx ~gvars ~ghosts s)
      |> Choice.map (fun (l1, l2) -> Literal.mk_and l1 l2)
  | SeqA (r, s) when is_nullable r ->
      Literal.join ~rctx ~gvars
        (next_literal ~rctx ~gvars ~ghosts r)
        (next_literal ~rctx ~gvars ~ghosts s)
  | SeqA (r, s) -> next_literal ~rctx ~gvars ~ghosts r
  | StarA r -> next_literal ~rctx ~gvars ~ghosts r
  (* TODO: can we do better? pruning? ordering? *)
  | ComplementA r ->
      let lits = next_literal ~rctx ~gvars ~ghosts r in
      Choice.(lits ++ delay (fun () -> return @@ Literal.neg_literals lits))
  | SetMinusA (AnyA, EventA sev) ->
      Choice.return @@ Literal.mk_not @@ Literal.of_sevent ~ghosts sev
  | SetMinusA (r, s) ->
      next_literal ~rctx ~gvars ~ghosts @@ LandA (r, ComplementA s)
(* _failatwith __FILE__ __LINE__ *)
(* @@ spf "next_literal: %s" @@ Rty.layout_regex r *)

let mk_complementA = function
  | EmptyA -> StarA AnyA
  | StarA AnyA -> EmptyA
  | r -> ComplementA r

let mk_orA r s =
  if r = EmptyA then s
  else if s = EmptyA then r
  else if r = StarA AnyA || s = StarA AnyA then StarA AnyA
  else if r = s then r
  else LorA (r, s)

let mk_andA r s =
  if r = EmptyA then EmptyA
  else if s = EmptyA then EmptyA
  else if r = StarA AnyA then s
  else if s = StarA AnyA then r
  else if (r = EpsilonA && is_nullable s) || (s = EpsilonA && is_nullable r)
  then EpsilonA
  else if r = s then r
  else match s with ComplementA s' when r = s' -> EmptyA | _ -> LandA (r, s)

let mk_seqA r s =
  if r = EpsilonA then s else if r = EmptyA then EmptyA else SeqA (r, s)

(** when `ghost = []`, it returns singleton choice *)
let symb_deriv_over_lit ~rctx ~gvars ?(ghosts = []) ?(index = 0) r lit =
  let ret sfa = [ ([], [], sfa) ] in
  let lit_match sev =
    match lit_entails_sev ~rctx ~gvars ~ghosts ~index lit sev with
    | Some (local, ghost) -> [ (local, ghost, EpsilonA) ]
    | None -> ret EmptyA
  in
  let lifted_complement = function
    | [ ([], [], r) ] -> ret @@ mk_complementA r
    | [ (local, [ rx ], r) ] ->
        let rx_neg = rx.rx #:: (neg_rty __FILE__ __LINE__ rx.rty) in
        [ (local, [ rx_neg ], mk_complementA r) ]
    | _ ->
        _failatwith __FILE__ __LINE__
          "symb_deriv_over_lit: complement corner case UNIMP"
  in
  (* TODO: join rxs appropriately
     the program logic here should be unified with how `rxs`
     are accumulated during repetivie derivative computation *)
  let lifted_and res_r res_s =
    List.cartesian_map
      (fun (local_r, ghost_r, r) (local_s, ghost_s, s) ->
        (local_r @ local_s, ghost_r @ ghost_s, mk_andA r s))
      res_r res_s
  in
  let lifted_or res_r res_s =
    match (res_r, res_s) with
    | [ ([], [], r) ], [ ([], [], s) ] -> ret @@ mk_orA r s
    (* TODO: this only covers simple case *)
    | _ -> res_r @ res_s
  in
  let lifted_seq res_r s =
    List.map
      (fun (local_r, ghost_r, r) -> (local_r, ghost_r, mk_seqA r s))
      res_r
  in
  let rec aux = function
    | EmptyA | EpsilonA -> ret EmptyA
    | AnyA -> ret EpsilonA
    | EventA sev -> lit_match sev
    | LorA (r, s) -> lifted_or (aux r) (aux s)
    | LandA (r, s) -> lifted_and (aux r) (aux s)
    | SeqA (r, s) when is_nullable r -> lifted_or (lifted_seq (aux r) s) (aux s)
    | SeqA (r, s) -> lifted_seq (aux r) s
    | StarA r -> lifted_seq (aux r) (StarA r)
    | ComplementA r -> lifted_complement (aux r)
    | SetMinusA (r, s) -> aux @@ LandA (r, ComplementA s)
  in
  (* TODO: see if simplify the result helps performance *)
  (* TODO: is the guard expensive? *)
  let* local, ghost, r = Choice.of_list @@ aux r in
  let* () = Choice.guard @@ not @@ is_empty r in
  Choice.return (r, local @ ghost)

let symb_deriv ~rctx ~gvars lit r =
  let open Literal in
  _assert __FILE__ __LINE__ "symb_deriv: lit is not bot"
  @@ not
  @@ is_bot_literal ~rctx ~gvars lit;
  if SRL.is_empty r then C.return (lit, r)
  else
    (* TODO: as only disjoint subsets of `lit` are of our interest,
       shall we combine `left_join` and `next_literal` together
       here? *)
    let* lit' =
      left_join ~rctx ~gvars (C.return lit) (next_literal ~rctx ~gvars r)
    in
    let* () = C.guard @@ not @@ is_bot_literal ~rctx ~gvars lit' in
    let* r', _ = symb_deriv_over_lit ~rctx ~gvars r lit' in
    C.return (lit', r')

(** TODO: since pre-condition SFA often begins with .*, will right
    deriv makes more sense here? *)
let symb_deriv_with_ghosts ~rctx ~gvars ~ghosts ~index lit r =
  let open Literal in
  _assert __FILE__ __LINE__ (spf "bottom literal: %s" @@ layout_literal lit)
  @@ not
  @@ is_bot_literal ~rctx ~gvars lit;
  if SRL.is_empty r then C.return (lit, r, [])
  else
    let* lit' =
      left_join ~rctx ~gvars (C.return lit)
        (next_literal ~rctx ~gvars ~ghosts r)
    in
    let* () = C.guard @@ not @@ is_bot_literal ~rctx ~gvars lit' in
    let* r', rxs = symb_deriv_over_lit ~rctx ~gvars ~ghosts ~index r lit' in
    C.return (lit', r', rxs)

let symb_quot ~rctx ~gvars trace regex =
  List.fold_left
    (fun ress lit ->
      let* tr_rev, regex = ress in
      let+ lit', regex' = symb_deriv ~rctx ~gvars lit regex in
      (lit' :: tr_rev, regex'))
    (Choice.return ([], regex))
    trace

let symb_match ?(rctx = []) ?(gvars = []) trace regex =
  symb_quot ~rctx ~gvars trace regex
  |> Choice.map (fun (_, r) -> is_nullable r)
  |> Choice.forall

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
