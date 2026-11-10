let minset_insert (x : Elem.t) : unit =
  if isWritten () then
    let (min : Elem.t) = read () in
    if elem_lt min x then ()
    else (
      insert x;
      ())
  else (
    insert x;
    write x;
    ())

(* Incorrectness specification: the minset_insert function can fail to insert
   elements that should be in the set, violating the invariant that all
   inserted elements should be members *)

let[@assertRty] minset_insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (Mem (x, false);
           IsWritten ((), true)) );
  }
