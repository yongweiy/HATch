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

(* The skip bug: copy stops at the first element that is not larger than the
   current maximum, so an element of the source set can be missing from the
   copy.  The iterator must not have been advanced yet and vl must already be
   in s when the iterator is created; otherwise a shallow witness exists
   (an iterator that already passed vl, or vl added after it was created). *)
let[@assertRty] copy ?l:(it = (true : [%v: Iter.t])) =
  {
    ret = (true : [%v: Set.t]);
    eff =
      (let (s : Set.t) = (true : [%v: Set.t]) in
       let (vl : Elem.t) = (true : [%v: Elem.t]) in
       Constrain
         ( (HasIter (it, s, true);
            Admit
              (_F
                 (Add ((vl [@d]), (s [@d]), u, true)
                 && _X (_F (GetIter ((s [@d]), (it [@d]), true)))));
            Admit (_G (not (Next ((it [@d]), b, true))))),
           (Mem (vl, s, true);
            Mem (vl, ret, false)) ));
  }
