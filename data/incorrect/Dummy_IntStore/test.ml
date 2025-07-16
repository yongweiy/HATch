let test (x: int) : bool =
  let (min : int) = read () in
  let (b : bool) = x < min in
  b

let[@assertRty] test ?l:(x = (true : [%v: int])) =
  {
    ret = (not v : [%v: bool]);
    eff = Reach(Write(x, ()));
  }
