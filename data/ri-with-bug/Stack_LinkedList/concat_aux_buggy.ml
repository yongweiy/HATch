let rec concat_aux (s1 : Cell.t) (s2 : Cell.t) : unit =
  if hasNext s1 then (
    let (s1' : Cell.t) = getNext s1 in
    concat_aux s1' s2;
    ())
  else if hasPrev s2 then ()
  (* else if cell_eq s1 s2 then () *)
  else (
    setNext s1 s2;
    ())

(* Incorrectness specification: the concat_aux function can create circular references
   by setting s1->next = s2 when s1 == s2, violating the representation invariant *)

let[@assertRty] concat_aux ?l:(s1 = (true : [%v: Cell.t]))
    ?l:(s2 = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (c : Key.t) = (true : [%v: Cell.t]) in
        Constrain ((), GetNext (c, c)));
  }
