let test (x : Node.t) : int =
  initVisited ();
  add x;
  let (y : Node.t) = take () in
  if node_eq x y then 1 else -1

let[@assertRty] test ?l:(x = (true : [%v: Node.t])) =
    { ret = (v == 1 : [%v: int]);
      eff = Constrain (IsEmpty ((), true), (IsEmpty ((), true))) }
