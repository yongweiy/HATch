(** labels for transitions in SFA *)

open Zzdatatype.Datatype
open Language
open Rty
open Sugar
open Syntax
open Utils
open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

type op_pred = Whitelist of string list | Blacklist of prop * string list
[@@deriving sexp, compare, equal, hash]

let subst_op_pred yz = function
  | Whitelist ops -> Whitelist ops
  | Blacklist (phi, ops) -> Blacklist (P.subst_prop yz phi, ops)

type literal = { events : eff_event list; op_pred : op_pred }
[@@deriving sexp, compare, equal, hash]
(** a literal denotes a disjunction of qualified events from `events`
    and other events whose `op` is conditioned by `op_filter`.
    a literal is well-formed if the disjuncted events are disjoint.
 *)

let mk_false = { events = []; op_pred = Whitelist [] }
let mk_true = { events = []; op_pred = Blacklist (P.mk_true, []) }

(** temporary holder for input/output args *)
let mk_event_from_op ?(phi = P.mk_true) op =
  { op; vs = []; v = Common.v_ret_name #: Nt.unit_ty; phi }

let subst yz { events; op_pred } =
  {
    events = List.map (SE.subst_ev yz) events;
    op_pred = subst_op_pred yz op_pred;
  }

(** TODO: this is weird, shall we abandon the rctx infrastructure? *)
let to_rxs ~index { events; op_pred } =
  match op_pred with
  | Whitelist [] ->
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
      rxs_of_xs (smart_or phis) vs
  | Whitelist _ -> [ (Rename.unique "u") #:: (mk_unit_rty_from_prop P.mk_true) ]
  | Blacklist (phi, _) ->
      [ (Rename.unique "u") #:: (mk_unit_rty_from_prop phi) ]

let to_phi { events; op_pred } =
  match op_pred with
  | Whitelist [] ->
      smart_or
      @@ List.map
           (fun { op; vs; v; phi } -> exists_ignore_unit (v :: vs) phi)
           events
  | Whitelist _ -> P.mk_true
  | Blacklist (phi, _) -> phi

let layout_literal { events; op_pred } =
  let event_strs = List.map (fun ev -> layout_sevent (EffEvent ev)) events in
  match op_pred with
  | Whitelist ops_include ->
      let strs = event_strs @ ops_include in
      if List.is_empty strs then "⊥" else String.concat " | " strs
  | Blacklist (phi, ops_exclude) when List.is_empty ops_exclude ->
      _assert __FILE__ __LINE__ "layout_literal: disjointness"
      @@ List.is_empty event_strs;
      layout_prop phi
  | Blacklist (phi, ops_exclude) ->
      String.concat " | " @@ event_strs
      @ [ layout_prop phi ^ "¬(" ^ String.concat " | " ops_exclude ^ ")" ]

let of_sevent = function
  | GuardEvent phi -> { events = []; op_pred = Blacklist (phi, []) }
  | EffEvent ev -> { events = [ ev ]; op_pred = Whitelist [] }

let inter_events evs1 evs2 =
  List.intersect_map
    (fun ev1 ev2 ->
      if String.equal ev1.op ev2.op then
        let ev = if List.is_empty ev1.vs then ev2 else ev1 in
        Some { ev with phi = smart_add_to ev2.phi ev1.phi }
      else None)
    evs1 evs2

let union_events evs1 evs2 =
  List.union_map
    (fun ev1 ev2 ->
      if String.equal ev1.op ev2.op then
        let ev = if List.is_empty ev1.vs then ev2 else ev1 in
        Some { ev with phi = smart_or [ ev2.phi; ev1.phi ] }
      else None)
    evs1 evs2

let inter_op_pred pred1 pred2 =
  match (pred1, pred2) with
  | Whitelist ops1, Whitelist ops2 ->
      { events = []; op_pred = Whitelist (StrList.intersect ops1 ops2) }
  | Whitelist ops, Blacklist (phi, ops_exclude)
  | Blacklist (phi, ops_exclude), Whitelist ops ->
      let ops = StrList.subtract ops ops_exclude in
      if is_true phi then { events = []; op_pred = Whitelist ops }
      else { events = List.map mk_event_from_op ops; op_pred = Whitelist [] }
  | Blacklist (phi1, ops_exclude1), Blacklist (phi2, ops_exclude2) ->
      {
        events = [];
        op_pred =
          Blacklist
            (smart_add_to phi2 phi1, StrList.union ops_exclude1 ops_exclude2);
      }

let union_op_pred pred1 pred2 =
  match (pred1, pred2) with
  | Whitelist ops1, Whitelist ops2 ->
      { events = []; op_pred = Whitelist (StrList.union ops1 ops2) }
  | Whitelist ops, Blacklist (phi, ops_exclude)
  | Blacklist (phi, ops_exclude), Whitelist ops ->
      if is_true phi then
        {
          events = [];
          op_pred = Blacklist (phi, StrList.subtract ops_exclude ops);
        }
      else
        {
          events = List.map mk_event_from_op ops;
          op_pred = Blacklist (phi, StrList.union ops_exclude ops);
        }
  | Blacklist (phi1, ops_exclude1), Blacklist (phi2, ops_exclude2)
    when is_true phi1 && is_true phi2 ->
      {
        events = [];
        op_pred =
          Blacklist (phi1, StrList.intersect ops_exclude1 ops_exclude2);
      }
  | Blacklist (phi1, ops_exclude1), Blacklist (phi2, ops_exclude2) ->
      {
        events =
          (List.map (mk_event_from_op ~phi:phi1)
          @@ StrList.subtract ops_exclude2 ops_exclude1)
          @ List.map (mk_event_from_op ~phi:phi2)
          @@ StrList.subtract ops_exclude1 ops_exclude2;
        op_pred =
          Blacklist
            (smart_or [ phi1; phi2 ], StrList.union ops_exclude1 ops_exclude2);
      }

let filter_events = function
  | Whitelist ops -> List.filter @@ fun ev -> List.mem ev.op ops
  | Blacklist (phi, ops) ->
      List.filter_map @@ fun ev ->
      if List.mem ev.op ops then None
      else Some { ev with phi = smart_add_to phi ev.phi }

let events_union_op_pred evs op_pred =
  match op_pred with
  | Whitelist ops ->
      {
        events = List.filter (fun ev -> not @@ List.mem ev.op ops) evs;
        op_pred;
      }
  | Blacklist (phi, ops) when is_true phi ->
      { events = List.filter (fun ev -> List.mem ev.op ops) evs; op_pred }
  | Blacklist (phi, ops) ->
      {
        events =
          List.map
            (fun ev ->
              if List.mem ev.op ops then ev
              else { ev with phi = smart_or [ ev.phi; phi ] })
            evs;
        op_pred =
          Blacklist (phi, StrList.union ops @@ List.map (fun ev -> ev.op) evs);
      }

let literal_union_events { events; op_pred } evs =
  let { events = evs; op_pred } = events_union_op_pred evs op_pred in
  { events = union_events events evs; op_pred }

(** It is sound to only consider either `guard` or `events`
    because of the way literals are emitted from the SFA.
   TODO: how much faster using syntactic approach instead of calling solver *)
let entails_sevent { events; op_pred } = function
  | GuardEvent phi' -> (
      let entails_ev { op; vs; v; phi } =
        Smtquery.check_bool @@ smart_implies phi phi'
      in
      match op_pred with
      | Blacklist (phi, _) when Smtquery.check_bool @@ smart_implies phi phi' ->
          List.for_all entails_ev events
      | Blacklist _ -> false
      | Whitelist [] -> List.for_all entails_ev events
      | Whitelist _ -> Smtquery.check_bool phi')
  | EffEvent ev' -> (
      match (events, op_pred) with
      | [ ev ], Whitelist [] when String.equal ev.op ev'.op ->
          Smtquery.check_bool @@ smart_implies ev.phi ev'.phi
      | [], Whitelist [ op ] when String.equal op ev'.op ->
          Smtquery.check_bool ev'.phi
      | _ -> false)

let is_bot_ev ~rctx ~substs ({ op; vs; v; phi } : eff_event) =
  check_prop ~rctx
  @@ forall_ignore_unit (v :: vs)
  @@ mk_not
  @@ List.fold_right subst_prop_id substs phi

(** determine if a literal is bottom, i.e., no satisfying events *)
let is_bot ~rctx ~substs { events; op_pred } =
  match op_pred with
  | Whitelist [] -> List.for_all (is_bot_ev ~rctx ~substs) events
  | Blacklist (phi, _) when Smtquery.check_bool @@ mk_not phi ->
      List.for_all (is_bot_ev ~rctx ~substs) events
  | _ -> false

(** an enhancement over `is_bot` by pruning out non-satisfiable branches
   TODO: add an option to enable over-approximation *)
let notbot_opt ?(rctx = []) ~substs ({ events; op_pred } as l) =
  let events = List.filter (not << is_bot_ev ~rctx ~substs) events in
  match op_pred with
  | Whitelist [] when List.is_empty events -> None
  | Blacklist (phi, _) when Smtquery.check_bool @@ mk_not phi ->
      if List.is_empty events then None
      else Some { events; op_pred = Whitelist [] }
  | _ -> Some { l with events }

let mk_not { events; op_pred } =
  let event_ops = List.map (fun ev -> ev.op) events in
  let dual_event (ev : eff_event) = { ev with phi = mk_not ev.phi } in
  let dual_events = List.map dual_event events in
  match op_pred with
  | Whitelist ops_include ->
      assert (StrList.is_disjoint ops_include event_ops);
      {
        events = dual_events;
        op_pred = Blacklist (P.mk_true, event_ops @ ops_include);
      }
  | Blacklist (phi, ops_exclude) when is_true phi ->
      assert (StrList.subset event_ops ops_exclude);
      {
        events = dual_events;
        op_pred = Whitelist (StrList.subtract ops_exclude event_ops);
      }
  | Blacklist (phi, ops_exclude) ->
      assert (StrList.subset event_ops ops_exclude);
      let events' =
        List.map mk_event_from_op @@ StrList.subtract ops_exclude event_ops
      in
      {
        events = dual_events @ events';
        op_pred = Blacklist (mk_not phi, ops_exclude);
      }

let mk_and l1 l2 =
  let evs0 = inter_events l1.events l2.events in
  let evs1 = filter_events l2.op_pred l1.events in
  let evs2 = filter_events l1.op_pred l2.events in
  let evs = evs0 @ evs1 @ evs2 in
  let l = inter_op_pred l1.op_pred l2.op_pred in
  literal_union_events l evs

let mk_or l1 l2 =
  let evs = union_events l1.events l2.events in
  let l = union_op_pred l1.op_pred l2.op_pred in
  literal_union_events l evs

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
