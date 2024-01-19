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
  (* let op_filter_str = *)
  (*   match op_filter with *)
  (*   | `Whitelist ops_include -> String.concat " | " ops_include *)
  (*   | `Blacklist ops_exclude when List.is_empty ops_exclude -> "" *)
  (*   | `Blacklist ops_exclude -> "¬(" ^ String.concat " | " ops_exclude ^ ")" *)
  (* in *)
  (* if op_filter_str = "" then events_str else events_str ^ " | " ^ op_filter_str *)
  match op_filter with
  | `Whitelist ops_include when List.is_empty ops_include -> events_str
  | `Whitelist ops_include -> String.concat " | " @@ (events_str :: ops_include)
  | `Blacklist ops_exclude
    when List.is_empty ops_exclude && List.is_empty events ->
      "⊤"
  | `Blacklist ops_exclude when List.is_empty events ->
      "¬(" ^ String.concat " | " ops_exclude ^ ")"
  | `Blacklist ops_exclude ->
      events_str ^ " | ¬(" ^ String.concat " | " ops_exclude ^ ")"

let print_trace tr =
  List.iter (fun l -> Pp.printf "%s; " @@ layout_literal l) tr;
  print_newline ()

let fv_event { op; vs; v; phi } =
  let vs = List.map (fun typed -> typed.x) (v :: vs) in
  let fvs = fv_prop phi in
  List.filter (fun v0 -> not (List.mem v0 vs)) fvs

let of_sevent ~ghosts = function
  | GuardEvent _ -> _failatwith __FILE__ __LINE__ "guard event literal unimp"
  | EffEvent ev -> (
      match StrList.intersect ghosts @@ fv_event ev with
      | [] -> { events = [ ev ]; op_filter = `Whitelist [] }
      | [ ghost ] ->
          (* TODO: assert the form of qualifier *)
          { events = [ { ev with phi = mk_true } ]; op_filter = `Whitelist [] }
      | _ ->
          _failatwith __FILE__ __LINE__
            "more than one ghost involved in a qualifier")

let print_query ~rctx ~gvars phi =
  Pp.printf "%s, %s ⊢ %s\n"
    (RTypectx.layout_typed_l rctx)
    (Rty.layout_typed_l Fun.id gvars)
    (layout_prop phi)

let check_prop ~rctx ~gvars phi =
  (* print_query ~rctx ~gvars phi; *)
  let rctx =
    RTypectx.new_to_rights rctx
    @@ List.map (fun { x; ty } -> { rx = x; rty = Rty.mk_top ty }) gvars
  in
  (* let rctx = *)
  (*   RTypectx.new_to_right rctx *)
  (*     { rx = Rename.unique "a"; rty = Rty.mk_unit_rty_from_prop phi } *)
  (* in *)
  let lhs_rty = Rty.mk_top Nt.unit_ty in
  (* let rhs_rty = Rty.mk_bot Nt.unit_ty in *)
  let rhs_rty = Rty.mk_unit_rty_from_prop phi in
  Subtyping.sub_rty_bool rctx (lhs_rty, rhs_rty)

let forall_ignore_unit us prop =
  List.fold_left
    (fun prop u -> if u.ty = Nt.unit_ty then prop else Forall (u, prop))
    prop us

let exists_ignore_unit us prop =
  List.fold_left
    (fun prop u -> if u.ty = Nt.unit_ty then prop else Exists (u, prop))
    prop us

let is_bot_literal ~rctx ~gvars { events; op_filter } =
  let aux ({ op; vs; v; phi } : eff_event) =
    check_prop ~rctx ~gvars @@ forall_ignore_unit (v :: vs) @@ mk_not phi
  in
  match op_filter with `Whitelist [] -> List.for_all aux events | _ -> false

let lit_entails_sev ~rctx ~gvars ~ghosts lit sev =
  (* TODO: guard event *)
  let ev =
    match sev with
    | EffEvent ev -> ev
    | GuardEvent _ ->
        _failatwith __FILE__ __LINE__ "lit_entails_sev: GuardEvent"
  in

  let entails ({ op = op1; vs = vs1; v = v1; phi = phi1 } : eff_event)
      ({ op = op2; vs = vs2; v = v2; phi = phi2 } : eff_event) =
    _assert __FILE__ __LINE__ "sev_entails_sev: op" (op1 = op2);
    _assert __FILE__ __LINE__ "sev_entails_sev: vs" (vs1 = vs2);
    _assert __FILE__ __LINE__ "sev_entails_sev: v" (v1 = v2);
    check_prop ~rctx ~gvars
    @@ forall_ignore_unit (v1 :: vs1)
    @@ smart_implies phi1 phi2
  in
  let opt_of_bool elem b = if b then Some elem else None in
  match lit with
  | { events = [ ev' ]; op_filter = `Whitelist [] } when ev'.op = ev.op -> (
      match StrList.intersect ghosts @@ fv_event ev with
      | [] -> opt_of_bool [] @@ entails ev' ev
      | [ ghost ] -> (
          let v_opt =
            List.find_map
              (fun v ->
                if ev.phi = mk_prop_var_eq_lit v @@ AVar ghost then Some v
                else None)
              (ev.v :: ev.vs)
          in
          match v_opt with
          | None ->
              _failatwith __FILE__ __LINE__
                "non-equality qualifier on ghost variable unimp"
          | Some v ->
              let vs =
                List.substract
                  (fun { x; _ } { x = y; _ } -> String.equal x y)
                  ev.vs [ v ]
              in
              let rty =
                mk_rty_var_sat_prop v @@ exists_ignore_unit vs ev'.phi
              in
              opt_of_bool [ ghost #:: rty ]
              @@ entails ev' { ev with phi = mk_true })
      | _ ->
          _failatwith __FILE__ __LINE__
            "more than one ghost involved in a qualifier")
  | { events = []; op_filter = `Whitelist [ op ] } when ev.op = op ->
      opt_of_bool [] @@ entails { ev with phi = mk_true } ev
  | { events = []; op_filter = `Blacklist ops } -> opt_of_bool [] false
  | _ -> opt_of_bool [] false

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

let neg_literals lits = mk_not @@ mk_or_multi @@ Choice.run_all lits

let join ~rctx ~gvars lits1 lits2 =
  let open Choice in
  (* Pp.printf "lits1: "; *)
  (* iter lits1 (fun lit1 -> *)
  (*     Pp.printf "%s, " @@ layout_literal lit1; *)
  (*     true); *)
  (* print_newline (); *)
  (* Pp.printf "lits2: "; *)
  (* iter lits2 (fun lit2 -> *)
  (*     Pp.printf "%s, " @@ layout_literal lit2; *)
  (*     true); *)
  (* print_newline (); *)
  let intersects = lift2 mk_and lits1 lits2 in
  let lits1_left =
    delay (fun () ->
        let neg_lit1 = neg_literals lits1 in
        if is_bot_literal ~rctx ~gvars neg_lit1 then fail
        else map (fun l2 -> mk_and neg_lit1 l2) lits2)
  in
  let lits2_left =
    delay (fun () ->
        let neg_lit2 = neg_literals lits2 in
        if is_bot_literal ~rctx ~gvars neg_lit2 then fail
        else map (fun l1 -> mk_and l1 neg_lit2) lits1)
  in
  let lits = intersects ++ lits1_left ++ lits2_left in
  (* Pp.printf "lits: "; *)
  (* iter lits (fun lit -> *)
  (*     Pp.printf "%s, " @@ layout_literal lit; *)
  (*     true); *)
  (* print_newline (); *)
  lits

let left_join ~rctx ~gvars lits1 lits2 =
  let open Choice in
  let intersects = lift2 mk_and lits1 lits2 in
  let lits2_left =
    delay (fun () ->
        let neg_lit2 = neg_literals lits2 in
        if is_bot_literal ~rctx ~gvars neg_lit2 then fail
        else map (fun l1 -> mk_and l1 neg_lit2) lits1)
  in
  intersects ++ lits2_left
