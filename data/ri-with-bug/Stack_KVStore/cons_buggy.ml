let rec cons (x : Elem.t) (s : Cell.t) : Cell.t =
  (* if existsValC s then s *)
  (* else *)
    let (c : Cell.t) = newCell () in
    if existsValC c then
      let (c' : Cell.t) = cons x s in
      c'
    else if existsC c then
      let (c' : Cell.t) = cons x s in
      c'
    else (
      putE c x;
      putC c s;
      c)

(* Incorrectness specification: the cons function can create cycles 
   by allowing a cell to point to itself as its next pointer *)

let[@assertRty] cons ?l:(x = (true : [%v: Elem.t]))
    ?l:(s = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Cell.t]);
    eff = Constrain ((), GetC (ret, ret));
  }
