let rec remove_aux (curr: int) (v: Elem.t) : unit =
  let (next : int) = getNext curr in
  if next == 0 then ()
  else if elem_eq (getVal next) v then
    (putNext curr (getNext next); ())
  else remove_aux next v

let[@assertRty] remove_aux ((a : int) [@ghost]) ((b : int) [@ghost])
     ?l:(hd = (b != 0 : [%v: int])) ?l:(vl = (true : [%v: Elem.t])) =
  { pre = nextP a b; res = (true : [%v: unit]);
    post = (nextP a b; rI a b)
  }
