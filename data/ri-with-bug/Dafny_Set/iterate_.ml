let copy (it1 : Iter.t) (s2 : Set.t) : unit =
  let rec loop : unit -> unit =
   fun (_ : unit) ->
    if hasNext it1 then (
      let (a : Elem.t) = next it1 in
      add a s2;
      loop ();
      ())
  in
  loop ();
  ()

let[@assertRty] copy ?l:(it1 = (true : [%v: Iter.t]))
    ?l:(s2 = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (s1 : Set.t) = (true : [%v: Set.t]) in
       let (vl : Elem.t) = (true : [%v: Elem.t]) in
       Constrain
         ( (HasIter (it1, s1, true);
            IsEmpty (s2, true)),
           (Mem (vl, s1, false);
            Mem (vl, s2, true)) ));
  }
