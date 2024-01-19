let incr (u : unit) : unit =
  let (curr : int) = read () in
  write (curr + 1);
  ()

let[@assertRty] incr ((c : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
