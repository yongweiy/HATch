let rec append (hd : Cell.t) (x : Elem.t) : unit =
  if isCell hd then
    if hasCellContent hd then
      let (c : Cell.t) = newCell () in
      setNext hd c;
      putCellContent c x;
      ()
    else (
      putCellContent hd x;
      ())
  else ()

(* Incorrectness specification: the append function can create circular references
   by setting hd->next = c when hd == c, violating the representation invariant *)

let[@assertRty] append ?l:(hd = (true : [%v: Cell.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Constrain ((), SetNext (hd, hd, ()));
  }
