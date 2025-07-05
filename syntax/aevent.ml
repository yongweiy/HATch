module F (L : Lit.T) = struct
  open Sexplib.Std
  open Ppx_compare_lib.Builtin
  open Ppx_hash_lib.Std.Hash.Builtin
  open Zzdatatype.Datatype
  open Sugar
  open Common

  (* open Srl.F (L) *)
  include Sevent.F (L)
  (* module Q = Qualifier.F (L) *)

  type phi = P.prop [@@deriving sexp, compare, equal, hash]

  type op_pred = Whitelist of string list | Blacklist of phi * string list
  [@@deriving sexp, compare, equal, hash]

  let subst_op_pred yz = function
    | Whitelist ops -> Whitelist ops
    | Blacklist (phi, ops) -> Blacklist (subst_prop yz phi, ops)

  type pred = { events : eff_event list; op_pred : op_pred }
  [@@deriving sexp, compare, equal, hash]
  (** a literal denotes a disjunction of qualified events from `events`
    and other events whose `op` is conditioned by `op_filter`.
    a literal is well-formed if the disjuncted events are disjoint.
 *)

  let mk_top = { events = []; op_pred = Blacklist (mk_true, []) }
  let mk_bot = { events = []; op_pred = Whitelist [] }

  let of_sevent = function
    | GuardEvent phi -> { events = []; op_pred = Blacklist (phi, []) }
    | EffEvent ev -> { events = [ ev ]; op_pred = Whitelist [] }

  (** temporary holder for input/output args *)
  let mk_event_from_op ?(phi = P.mk_true) op =
    { op; vs = []; v = v_ret_name #: unit_ty; phi }

  let fv_op_pred = function
    | Blacklist (phi, _) -> fv_prop phi
    | Whitelist _ -> []

  let fv_pred { events; op_pred } =
    fv_op_pred op_pred @ List.concat_map fv_eff_event events

  let subst_pred yz { events; op_pred } =
    {
      events = List.map (subst_ev yz) events;
      op_pred = subst_op_pred yz op_pred;
    }

  let normalize_name_pred { events; op_pred } =
    { events = List.map normalize_name_eff_event events; op_pred }

  let from_prop phi = { events = []; op_pred = Blacklist (phi, []) }

  let to_prop { events; op_pred } =
    match op_pred with
    | Whitelist [] ->
        mk_or_multi
        @@ List.map
             (fun { op; vs; v; phi } -> smart_multi_exists (v :: vs) phi)
             events
    | Whitelist _ -> P.mk_true
    | Blacklist (phi, _) -> phi

  let of_sevent = function
    | GuardEvent phi -> { events = []; op_pred = Blacklist (phi, []) }
    | EffEvent ev -> { events = [ ev ]; op_pred = Whitelist [] }

  let inter_events evs1 evs2 =
    List.intersect_map
      (fun ev1 ev2 ->
        if String.equal ev1.op ev2.op then
          let ev = if List.is_empty ev1.vs then ev2 else ev1 in
          Some { ev with phi = mk_and ev2.phi ev1.phi }
        else None)
      evs1 evs2

  let union_events evs1 evs2 =
    List.union_map
      (fun ev1 ev2 ->
        if String.equal ev1.op ev2.op then
          let ev = if List.is_empty ev1.vs then ev2 else ev1 in
          Some { ev with phi = mk_or ev2.phi ev1.phi }
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
            Blacklist (mk_and phi2 phi1, StrList.union ops_exclude1 ops_exclude2);
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
          op_pred = Blacklist (phi1, StrList.intersect ops_exclude1 ops_exclude2);
        }
    | Blacklist (phi1, ops_exclude1), Blacklist (phi2, ops_exclude2) ->
        {
          events =
            (List.map (mk_event_from_op ~phi:phi1)
            @@ StrList.subtract ops_exclude2 ops_exclude1)
            @ List.map (mk_event_from_op ~phi:phi2)
            @@ StrList.subtract ops_exclude1 ops_exclude2;
          op_pred =
            Blacklist (mk_or phi1 phi2, StrList.union ops_exclude1 ops_exclude2);
        }

  let filter_events = function
    | Whitelist ops -> List.filter @@ fun ev -> List.mem ev.op ops
    | Blacklist (phi, ops) ->
        List.filter_map @@ fun ev ->
        if List.mem ev.op ops then None
        else Some { ev with phi = mk_and phi ev.phi }

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
                else { ev with phi = mk_or ev.phi phi })
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
  let entails_sevent ~check { events; op_pred } = function
    | GuardEvent phi' -> (
        let entails_ev { op; vs; v; phi } = check @@ smart_implies phi phi' in
        match op_pred with
        | Blacklist (phi, _) when check @@ smart_implies phi phi' ->
            List.for_all entails_ev events
        | Blacklist _ -> false
        | Whitelist [] -> List.for_all entails_ev events
        | Whitelist _ -> check phi')
    | EffEvent ev' -> (
        match (events, op_pred) with
        | [ ev ], Whitelist [] when String.equal ev.op ev'.op ->
            check @@ smart_implies ev.phi ev'.phi
        | [], Whitelist [ op ] when String.equal op ev'.op -> check ev'.phi
        | _ -> false)

  let entails ~is_sat ev1 ev2 =
    _failatwith __FILE__ __LINE__ "TODO: AEvent.entails unimplemented"

  (* let check_prop ~rctx phi = *)
  (*   (\* print_query ~rctx ~gvars phi; *\) *)
  (*   (\* let rctx = *\) *)
  (*   (\*   RTypectx.new_to_rights rctx *\) *)
  (*   (\*   @@ List.map (fun { x; ty } -> { rx = x; rty = Rty.mk_top ty }) gvars *\) *)
  (*   (\* in *\) *)
  (*   (\* let rctx = *\) *)
  (*   (\*   RTypectx.new_to_right rctx *\) *)
  (*   (\*     { rx = Rename.unique "a"; rty = Rty.mk_unit_rty_from_prop phi } *\) *)
  (*   (\* in *\) *)
  (*   let lhs_rty = Rty.mk_top Nt.unit_ty in *)
  (*   (\* let rhs_rty = Rty.mk_bot Nt.unit_ty in *\) *)
  (*   let rhs_rty = Rty.mk_unit_rty_from_prop phi in *)
  (*   Subtyping.sub_rty_bool rctx (lhs_rty, rhs_rty) *)

  let is_bot_ev ~is_bot ({ op; vs; v; phi } : eff_event) =
    is_bot @@ smart_multi_forall (v :: vs) phi

  (** determine if a literal is bottom, i.e., no satisfying events *)
  let is_bot ~is_bot { events; op_pred } =
    match op_pred with
    | Whitelist [] -> List.for_all (is_bot_ev ~is_bot) events
    | Blacklist (phi, _) when is_bot @@ mk_not phi ->
        List.for_all (is_bot_ev ~is_bot) events
    | _ -> false

  (** an enhancement over `is_bot` by pruning out non-satisfiable branches
   TODO: add an option to enable over-approximation *)
  let simp_opt ~is_bot ({ events; op_pred } as l) =
    let events = List.filter (not << is_bot_ev ~is_bot) events in
    match op_pred with
    | Whitelist [] when List.is_empty events -> None
    | Blacklist (phi, _) when is_bot @@ mk_not phi ->
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

  let mk_or_list lits =
    let rec aux acc = function
      | [] -> acc
      | lit :: lits -> aux (mk_or acc lit) lits
    in
    match lits with [] -> mk_bot | lit :: lits -> aux lit lits

  let mk_and_list lits =
    let rec aux acc = function
      | [] -> acc
      | lit :: lits -> aux (mk_and acc lit) lits
    in
    match lits with [] -> mk_top | lit :: lits -> aux lit lits

  let join lits1 lits2 =
    List.cartesian_map mk_and lits1 lits2
    @ List.map (mk_and (mk_not @@ mk_or_list lits2)) lits1
    @ List.map (mk_and (mk_not @@ mk_or_list lits1)) lits2

  type ev = { op : string; args : lit typed list; ret : lit typed }
  [@@deriving sexp, compare, equal, hash]

  type func = IdentityF | EventF of ev [@@deriving sexp, compare, equal, hash]

  let mk_ident = IdentityF
  let mk_const ev = EventF ev

  let force_const = function
    | IdentityF -> _failatwith __FILE__ __LINE__ "die"
    | EventF ev -> ev

  let subst_ev yz { op; args; ret } =
    let aux = subst_lit yz in
    { op; args = List.map (( #-> ) aux) args; ret = aux #-> ret }

  let subst_func yz = function
    | IdentityF -> IdentityF
    | EventF ev -> EventF (subst_ev yz ev)

  let fv_ev { op; args; ret } = List.concat_map fv_typed_lit (ret :: args)
  let fv_func = function IdentityF -> [] | EventF ev -> fv_ev ev

  let ev_to_pred { op; args; ret } =
    let tys = List.map (fun { ty; _ } -> ty) args in
    let vs = vs_names_from_types tys in
    let v = v_ret_name #: ret.ty in
    let phi =
      And
        (List.map2
           (fun y z -> Lit (mk_lit_eq_lit y.ty (AVar y.x) z.x))
           (v :: vs) (ret :: args))
    in
    { op_pred = Whitelist []; events = [ { op; vs; v; phi } ] }

  (** in case we need to check functionality of SFTs *)
  let mk_disequal sev f g =
    match (f, g) with
    | IdentityF, IdentityF -> mk_bot
    | IdentityF, EventF ev | EventF ev, IdentityF ->
        mk_and sev @@ mk_not @@ ev_to_pred ev
    | EventF ev1, EventF ev2 ->
        let sev1 = ev_to_pred ev1 in
        let sev2 = ev_to_pred ev2 in
        mk_and sev
        @@ mk_or (mk_and sev1 @@ mk_not sev2) (mk_and sev2 @@ mk_not sev1)

  (** [compose f g = fun x -> f (g x)] *)
  let compose f = function
    | IdentityF -> f
    | EventF ev -> ( match f with IdentityF -> EventF ev | EventF _ -> f)

  let mk_preimage sev = function
    | IdentityF -> sev
    | EventF ev -> mk_and sev @@ ev_to_pred ev

  (** Miss global constraint in theory but should be safe in practice *)
  let mk_image sev = function IdentityF -> sev | EventF ev -> ev_to_pred ev
end
