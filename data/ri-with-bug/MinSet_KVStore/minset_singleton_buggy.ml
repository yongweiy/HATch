let rec minset_singleton (x : Elem.t) : bool =
  if isWritten () then false
  else
    let (k : Key.t) = randomKey () in
    if exists k then
      let (res : bool) = minset_singleton x in
      res
    else (
      write x;
      (* put k x; *)
      true)

(* Incorrectness specification: the minset_singleton function can write an element
   without putting it into the KVStore, violating the invariant that written elements
   should be stored in the KVStore *)

let[@assertRty] minset_singleton ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Constrain
        ( (),
          (IsWritten ((), true);
           HasValue (x, false)) );
  }
