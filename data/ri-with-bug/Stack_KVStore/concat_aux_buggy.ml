let rec concat_aux (s1 : Cell.t) (s2 : Cell.t) : unit =
  if existsC s1 then (
    let (s1' : Cell.t) = getC s1 in
    concat_aux s1' s2;
    ())
  (* else if existsValC s2 then () *)
  else (
    putC s1 s2;
    ())

(* Incorrectness specification: the concat_aux function can create cycles 
   by allowing a cell to point to itself as its next pointer *)

let[@assertRty] concat_aux ?l:(s1 = (true : [%v: Cell.t])) 
    ?l:(s2 = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Constrain ((), GetC (s1, s1));
  }
