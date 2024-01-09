(** the equivalence class for computing derivative *)

open Zzdatatype.Datatype
open Language
open Rty
open Sugar
open Syntax

(* module Q = Qualifier *)

let with_same_op ev1 ev2 = String.equal ev1.op ev2.op

type literal = {
  events : eff_event list;
  op_filter : [ `Whitelist of string list | `Blacklist of string list ];
}
(** the literal denotes the disjunction between event from `events`
    and other events whose `op` is conditioned by `op_filter`; the
    disjunction is guaranteed to be disjoint
    
    TODO: need to account for guard event
*)

let layout_literal { events; op_filter } =
  let events_str =
    String.concat " | "
    @@ List.map (fun ev -> layout_sevent (EffEvent ev)) events
  in
  let op_filter_str =
    match op_filter with
    | `Whitelist ops_include -> String.concat " | " ops_include
    | `Blacklist ops_exclude when List.is_empty ops_exclude -> ""
    | `Blacklist ops_exclude -> "¬(" ^ String.concat " | " ops_exclude ^ ")"
  in
  if op_filter_str = "" then events_str else events_str ^ " | " ^ op_filter_str

let print_trace =
  List.iter (fun l -> Pp.printf "%s; " @@ layout_literal l)

let of_sevent = function
  | GuardEvent _ -> _failatwith __FILE__ __LINE__ "guard event literal unimp"
  | EffEvent ev -> { events = [ ev ]; op_filter = `Whitelist [] }

let mk_false = { events = []; op_filter = `Whitelist [] }
let mk_true = { events = []; op_filter = `Blacklist [] }

let mk_not { events; op_filter } =
  let event_ops = List.map (fun ev -> ev.op) events in
  let dual_event (ev : eff_event) = { ev with phi = mk_not ev.phi } in
  let dual_events = List.map dual_event events in
  match op_filter with
  | `Whitelist ops_include ->
      assert (StrList.is_disjoint ops_include event_ops);
      { events = dual_events; op_filter = `Blacklist (event_ops @ ops_include) }
  | `Blacklist ops_exclude ->
      assert (StrList.subset event_ops ops_exclude);
      {
        events = dual_events;
        op_filter = `Whitelist (StrList.subtract ops_exclude event_ops);
      }

let mk_and l1 l2 =
  let rec join_and_sub inter diff = function
    | [] -> (inter, diff)
    | ev :: evs -> (
        match List.find_opt (with_same_op ev) l2.events with
        | Some ev' ->
            let ev = { ev with phi = smart_and [ ev.phi; ev'.phi ] } in
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
          `Blacklist (ops_exclude1 @ ops_exclude),
          `Blacklist ops_exclude2 )
  in
  (* TODO: is it really more efficient to use `op_subfilterX` instead
     of `op_filterX` *)
  let events =
    events_inter
    @ filter_events_by_op events_sub1 op_subfilter2
    @ filter_events_by_op events_sub2 op_subfilter1
  in
  { events; op_filter }

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
  { events; op_filter }

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

let is_false ?(constr = P.mk_true) { events; op_filter } =
  let aux ({ phi; _ } : eff_event) =
    not @@ Smtquery.check_sat_bool @@ smart_and [ constr; phi ]
  in
  match op_filter with `Whitelist [] -> List.for_all aux events | _ -> false

let neg_literals lits = mk_not @@ mk_or_multi @@ Choice.run_all lits

let join ?(constr = P.mk_true) lits1 lits2 =
  let intersects =
    Choice.product lits1 lits2 |> Choice.map (fun (l1, l2) -> mk_and l1 l2)
  in
  let lits1_left =
    Choice.delay (fun () ->
        let neg_lit1 = neg_literals lits1 in
        if is_false ~constr neg_lit1 then Choice.fail
        else Choice.map (fun l2 -> mk_and neg_lit1 l2) lits2)
  in
  let lits2_left =
    Choice.delay (fun () ->
        let neg_lit2 = neg_literals lits2 in
        if is_false ~constr neg_lit2 then Choice.fail
        else Choice.map (fun l1 -> mk_and l1 neg_lit2) lits1)
  in
  Choice.(intersects ++ lits1_left ++ lits2_left)

let left_join ?(constr = P.mk_true) lits1 lits2 =
  let intersects =
    Choice.product lits1 lits2 |> Choice.map (fun (l1, l2) -> mk_and l1 l2)
  in
  let lits2_left =
    Choice.delay (fun () ->
        let neg_lit2 = neg_literals lits2 in
        if is_false ~constr neg_lit2 then Choice.fail
        else Choice.map (fun l1 -> mk_and l1 neg_lit2) lits1)
  in
  Choice.(intersects ++ lits2_left)
