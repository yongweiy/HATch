(** labels for transitions in SFA *)

open Zzdatatype.Datatype
open Language
open Rty
open Sugar
open Syntax
open Utils

module Guard = struct
  type t = Pos of prop | Neg of prop [@@deriving sexp, compare, equal, hash]

  let apply guard phi =
    match guard with
    | Pos psi -> smart_and [ psi; phi ]
    | Neg psi -> smart_or [ mk_not psi; phi ]

  let is_trivial = function Pos phi | Neg phi -> is_true phi

  let layout = function
    | g when is_trivial g -> ""
    | Pos phi -> layout_prop phi ^ "⩓"
    | Neg phi -> layout_prop (mk_not phi) ^ "⩔"

  let mk_not = function Pos phi -> Neg phi | Neg phi -> Pos phi

  let mk_and = function
    | Pos phi1, Pos phi2 -> Pos (smart_and [ phi1; phi2 ])
    | guard, Neg phi | Neg phi, guard ->
        _assert __FILE__ __LINE__ "mk_and: non-trivial guard" @@ is_true phi;
        guard

  let mk_or = function
    | Neg phi1, Neg phi2 -> Neg (smart_or [ phi1; phi2 ])
    | guard, Pos phi | Pos phi, guard ->
        _assert __FILE__ __LINE__ "mk_or: non-trivial guard" @@ is_true phi;
        guard
end

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

type literal = {
  guard : Guard.t;
  events : eff_event list;
  op_filter : [ `Whitelist of string list | `Blacklist of string list ];
}
[@@deriving sexp, compare, equal, hash]
(** a literal denotes a disjunction of qualified events from `events`
    and other events whose `op` is conditioned by `op_filter`.
    `Pos` guard is interpreted as a conjunct to each event qualifier;
    `Neg` guard is interpreted as a disjunct to each event qualifier.
    a literal is well-formed if the disjuncted events are disjoint.
*)

let subst yz l = { l with events = List.map (SE.subst_ev yz) l.events }

(** TODO: this is weird, shall we abandon the rctx infrastructure? *)
let to_rxs ~index { guard; events; op_filter } =
  match op_filter with
  | `Whitelist [] ->
      let vs, phis =
        events
        |> List.map (fun { op; vs; v; phi } ->
               let vs, substs =
                 rename_xs ~rename:(rename ~op ~index) @@ (v :: vs)
               in
               let phi = P.multisubst_prop_id substs phi in
               (vs, phi))
        |> List.fold_left
             (fun (vss, phis) (vs, phi) -> (vs @ vss, phi :: phis))
             ([], [])
      in
      let phi = Guard.apply guard @@ smart_or phis in
      rxs_of_xs phi vs
  | `Whitelist _ | `Blacklist _ ->
      [
        (Rename.unique "u")
        #:: (mk_unit_rty_from_prop @@ Guard.apply guard mk_true);
      ]

let to_phi { guard; events; op_filter } =
  match op_filter with
  | `Whitelist [] ->
      Guard.apply guard @@ smart_or
      @@ List.map (fun { op; vs; v; phi } -> exists_ignore_unit (v :: vs) phi) events
  | `Whitelist _ | `Blacklist _ -> Guard.apply guard mk_true

let layout_literal { guard; events; op_filter } =
  let event_strs = List.map (fun ev -> layout_sevent (EffEvent ev)) events in
  Guard.layout guard
  ^
  match op_filter with
  | `Whitelist ops_include ->
      let strs = event_strs @ ops_include in
      if List.is_empty strs then "⊥" else String.concat " | " strs
  | `Blacklist ops_exclude when List.is_empty ops_exclude ->
      _assert __FILE__ __LINE__ "layout_literal: disjointness"
      @@ List.is_empty event_strs;
      "⊤"
  | `Blacklist ops_exclude ->
      String.concat " | " @@ event_strs
      @ [ "¬(" ^ String.concat " | " ops_exclude ^ ")" ]

let of_sevent = function
  | GuardEvent phi ->
      { guard = Pos phi; events = []; op_filter = `Whitelist [] }
  | EffEvent ev ->
      { guard = Pos mk_true; events = [ ev ]; op_filter = `Whitelist [] }

(** It is sound to only consider either `guard` or `events`
    because of the way literals are emitted from the SFA.
   TODO: how much faster using syntactic approach instead of calling solver *)
let entails_sevent { guard; events; op_filter } = function
  | GuardEvent phi' -> (
      match guard with
      | Pos phi -> Smtquery.check_bool @@ smart_implies phi phi'
      | Neg _ -> _failatwith __FILE__ __LINE__ "unimp")
  | EffEvent ev' -> (
      _assert __FILE__ __LINE__ "unimp"
        (match guard with
        | Neg phi when not @@ is_true phi -> false
        | _ -> true);
      match (events, op_filter) with
      | [ ev ], `Whitelist [] when String.equal ev.op ev'.op ->
          Smtquery.check_bool @@ smart_implies ev.phi ev'.phi
      | [], `Whitelist [ op ] when String.equal op ev'.op ->
          Smtquery.check_bool @@ smart_implies mk_true ev'.phi
      | _ -> false)

(** determine if a literal is bottom, i.e., no satisfying events *)
let is_bot ~rctx ~substs { guard; events; op_filter } =
  let aux ({ op; vs; v; phi } : eff_event) =
    check_prop ~rctx
    @@ forall_ignore_unit (v :: vs)
    @@ mk_not @@ Guard.apply guard
    @@ List.fold_right subst_prop_id substs phi
  in
  match op_filter with `Whitelist [] -> List.for_all aux events | _ -> false

(** an enhancement over `is_bot` by pruning out non-satisfiable branches
   TODO: add an option to enable over-approximation *)
let notbot_opt ?(rctx = []) ~substs ({ guard; events; op_filter } as l) =
  let is_bot_ev ({ op; vs; v; phi } as ev : eff_event) =
    check_prop ~rctx
    @@ forall_ignore_unit (v :: vs)
    @@ mk_not @@ Guard.apply guard
    @@ List.fold_right subst_prop_id substs phi
  in
  let events = List.filter (not << is_bot_ev) events in
  match op_filter with
  | `Whitelist [] when List.is_empty events -> None
  | _ -> Some { l with events }

let mk_false = { guard = Pos mk_true; events = []; op_filter = `Whitelist [] }
let mk_true = { guard = Pos mk_true; events = []; op_filter = `Blacklist [] }

let mk_not { guard; events; op_filter } =
  let event_ops = List.map (fun ev -> ev.op) events in
  let dual_event (ev : eff_event) = { ev with phi = mk_not ev.phi } in
  let dual_events = List.map dual_event events in
  match op_filter with
  | `Whitelist ops_include ->
      assert (StrList.is_disjoint ops_include event_ops);
      {
        guard = Guard.mk_not guard;
        events = dual_events;
        op_filter = `Blacklist (event_ops @ ops_include);
      }
  | `Blacklist ops_exclude ->
      assert (StrList.subset event_ops ops_exclude);
      {
        guard = Guard.mk_not guard;
        events = dual_events;
        op_filter = `Whitelist (StrList.subtract ops_exclude event_ops);
      }

let mk_and l1 l2 =
  let rec join_and_sub inter diff = function
    | [] -> (inter, diff)
    | ev :: evs -> (
        match List.find_opt (with_same_op ev) l2.events with
        | Some ev' ->
            let ev = { ev with phi = smart_add_to ev'.phi ev.phi } in
            join_and_sub (ev :: inter) diff evs
        | None -> join_and_sub inter (ev :: diff) evs)
  in
  let filter_events_by_op evs op_filter =
    match op_filter with
    | `Whitelist ops_include ->
        List.filter (fun ev -> List.mem ev.op ops_include) evs
    | `Blacklist ops_exclude ->
        List.filter (fun ev -> not @@ List.mem ev.op ops_exclude) evs
  in
  let events_inter, events_sub1 = join_and_sub [] [] l1.events in
  let events_sub2 = List.substract with_same_op l2.events events_inter in
  let op_filter, op_subfilter1, op_subfilter2 =
    match (l1.op_filter, l2.op_filter) with
    | `Whitelist ops_include1, `Whitelist ops_include2 ->
        let ops_include, ops_include_sub1 =
          StrList.intersect_and_subtract ops_include1 ops_include2
        in
        let ops_include_sub2 = StrList.subtract ops_include2 ops_include in
        ( `Whitelist ops_include,
          `Whitelist ops_include_sub1,
          `Whitelist ops_include_sub2 )
    | `Whitelist ops_include, `Blacklist ops_exclude ->
        let ops_include_excluded, ops_include_sub =
          StrList.intersect_and_subtract ops_include ops_exclude
        in
        let ops_exclude = ops_exclude @ ops_include_sub in
        ( `Whitelist ops_include_sub,
          `Whitelist ops_include_excluded,
          `Blacklist ops_exclude )
    | `Blacklist ops_exclude, `Whitelist ops_include ->
        let ops_include_excluded, ops_include_sub =
          StrList.intersect_and_subtract ops_include ops_exclude
        in
        let ops_exclude = ops_exclude @ ops_include_sub in
        ( `Whitelist ops_include_sub,
          `Blacklist ops_exclude,
          `Whitelist ops_include_excluded )
    | `Blacklist ops_exclude1, `Blacklist ops_exclude2 ->
        let ops_exclude = StrList.union ops_exclude1 ops_exclude2 in
        ( `Blacklist ops_exclude,
          `Whitelist (StrList.subtract ops_exclude2 ops_exclude1),
          `Whitelist (StrList.subtract ops_exclude1 ops_exclude2) )
  in
  (* TODO: is it really more efficient to use `op_subfilterX` instead
     of `op_filterX` *)
  let events =
    events_inter
    @ filter_events_by_op events_sub1 op_subfilter2
    @ filter_events_by_op events_sub2 op_subfilter1
  in
  let guard = Guard.mk_and (l1.guard, l2.guard) in
  { guard; events; op_filter }

let mk_or l1 l2 =
  let rec join_and_sub inter diff = function
    | [] -> (inter, diff)
    | ev :: evs -> (
        match List.find_opt (with_same_op ev) l2.events with
        | Some ev' ->
            let ev = { ev with phi = smart_or [ ev.phi; ev'.phi ] } in
            join_and_sub (ev :: inter) diff evs
        | None -> join_and_sub inter (ev :: diff) evs)
  in
  let discard_events_by_op evs op_filter =
    match op_filter with
    | `Whitelist ops_include ->
        List.filter (fun ev -> not @@ List.mem ev.op ops_include) evs
    | `Blacklist ops_exclude ->
        List.filter (fun ev -> List.mem ev.op ops_exclude) evs
  in
  let events_inter, events_sub1 = join_and_sub [] [] l1.events in
  let events_sub2 = List.substract with_same_op l2.events events_inter in
  let events_sub1 = discard_events_by_op events_sub1 l2.op_filter in
  let events_sub2 = discard_events_by_op events_sub2 l1.op_filter in
  let events = events_inter @ events_sub1 @ events_sub2 in
  let op_filter =
    match (l1.op_filter, l2.op_filter) with
    | `Whitelist ops_include1, `Whitelist ops_include2 ->
        `Whitelist (StrList.union ops_include1 ops_include2)
    | `Whitelist ops_include, `Blacklist ops_exclude
    | `Blacklist ops_exclude, `Whitelist ops_include ->
        `Blacklist (StrList.subtract ops_exclude ops_include)
    | `Blacklist ops_exclude1, `Blacklist ops_exclude2 ->
        `Blacklist (StrList.intersect ops_exclude1 ops_exclude2)
  in
  let guard = Guard.mk_or (l1.guard, l2.guard) in
  { guard; events; op_filter }

let mk_or_multi lits =
  let rec aux acc = function
    | [] -> acc
    | lit :: lits -> aux (mk_or acc lit) lits
  in
  match lits with [] -> mk_false | lit :: lits -> aux lit lits

let mk_and_multi lits =
  let rec aux acc = function
    | [] -> acc
    | lit :: lits -> aux (mk_and acc lit) lits
  in
  match lits with [] -> mk_true | lit :: lits -> aux lit lits

let neg_literals lits = mk_not @@ mk_or_multi @@ lits

let join lits1 lits2 =
  List.cartesian_map mk_and lits1 lits2
  @ List.map (mk_and (neg_literals lits2)) lits1
  @ List.map (mk_and (neg_literals lits1)) lits2
