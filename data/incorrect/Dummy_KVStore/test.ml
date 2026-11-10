let test (x: Elem.t) : bool =
  let (min : Elem.t) = read () in
  let (b : bool) = elem_lt x min in
  b

let[@assertRty] test ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (not v : [%v: bool]);
    eff = Constrain((), Write(x, ()));
  }
