let rec remove_aux (curr: Ptr.t) (v: Elem.t) : unit =
  let (next : Ptr.t) = getNext curr in
  if is_nullptr next then ()
  else if elem_eq (getVal next) v then
    (putNext curr (getNext next); ())
  else remove_aux next v

let[@assertRty] remove_aux ((a1 : Ptr.t) [@ghost]) ((a2 : Ptr.t) [@ghost])
     ?l:(hd = (not (is_nullptr a2) : [%v: Ptr.t])) ?l:(vl = (true : [%v: Elem.t])) =
  { pre = nextP a1 a2; res = (true : [%v: unit]);
    post = (nextP a1 a2; rI a1 a2)
  }
