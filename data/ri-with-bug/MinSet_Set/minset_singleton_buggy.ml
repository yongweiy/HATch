let minset_singleton (x : Elem.t) : bool =
  if isWritten () then false
  else (
    (* insert x; *)
    write x;
    true)

(* Incorrectness specification: the minset_singleton function can write an element
   without inserting it into the set, violating the invariant that written elements
   should be members of the set *)

let[@assertRty] minset_singleton ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Constrain
        ( (),
          (IsEmpty ((), true);
           IsWritten ((), true)) );
  }
