let copy (it : Iter.t) : Set.t =
  let (res : Set.t) = create () in
  let rec loop : Elem.t -> unit =
   fun (max : Elem.t) ->
    if hasNext it then
      let (a : Elem.t) = next it in
      if elem_lt max a then (
        add a res;
        loop a;
        ())
  in
  if hasNext it then (
    let (init : Elem.t) = next it in
    add init res;
    loop init;
    res)
  else res

(* HATch baseline only (scripts/run_paper_benchmarks.py HATCH_CLIENT_OVERRIDE).
   Same program and query as iterate.ml, written as an Htriple directly:
   Constrain_to_htriple cannot translate the query's Admit (...) conditions.
   Reachability reading (srlexec reach_mode): a witness starts from a history
   where it is s's only iterator, not yet advanced, and vl was added to s
   before it was created, and ends with vl in s but not in the result r. *)
let[@assertRty] copy ((s : Set.t) [@ghost]) ((vl : Elem.t) [@ghost]) ((r : Set.t) [@ghost])
    ?l:(it = (true : [%v: Iter.t])) =
  {
    pre =
      _U
        (not (GetIter (y, (it [@d]), true)))
        (GetIter ((s [@d]), (it [@d]), true)
        && _X (_G (not (GetIter (y, (it [@d]), true)))))
      && _F
           (Add ((vl [@d]), (s [@d]), u, true)
           && _X (_F (GetIter ((s [@d]), (it [@d]), true))))
      && _G (not (Next ((it [@d]), b, true)));
    res = (v == r : [%v: Set.t]);
    post =
      not
        (_F (Add ((vl [@d]), (s [@d]), u, true))
        && not (_F (Add ((vl [@d]), (r [@d]), u, true))));
  }
