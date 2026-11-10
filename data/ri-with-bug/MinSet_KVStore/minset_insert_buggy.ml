let rec minset_insert (x : Elem.t) : unit =
  if isWritten () then
    if hasValue x then ()
    else
      let (k : Key.t) = randomKey () in
      (* if exists k then ( *)
        (* minset_insert x; *)
        (* ()) *)
      (* else *)
        let (min : Elem.t) = read () in
        if elem_lt min x then ()
        else (
          put k x;
          ())
  else ()

(* Incorrectness specification: the minset_insert function can fail to insert
   elements that should be in the KVStore, violating the invariant that all
   inserted elements should be stored *)

let[@assertRty] minset_insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (HasValue (x, false);
           IsWritten ((), true)) );
  }
