let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  if hasPrev s then s
  else
    let (c : Cell.t) = newCell () in
    if not (cell_eq c s) then
      let (c' : Cell.t) = cons x s in
      c'
    else (
      putCellContent c x;
      setNext c s;
      c)

(* Incorrectness specification: the cons function can create circular references
   by setting c->next = c when c == s, violating the representation invariant *)

let[@assertRty] cons ?l:(x = (true : [%v: Elem.t]))
    ?l:(s = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Cell.t]);
    eff = Constrain (HasPrev (s, false), GetNext (ret, ret));
  }
