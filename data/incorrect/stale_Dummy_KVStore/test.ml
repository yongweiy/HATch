let test (x: Elem.t) : bool =
  let (min : Elem.t) = read () in
  let (b : bool) = elem_lt x min in
  b

let[@assertSRLRty] test ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (not v : [%v: bool]);
    trans = Post(starL(atomL (Any true)));
  }
