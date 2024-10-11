let minset_insert (x : Elem.t) : unit =
  if isWritten () then
    let (min : Elem.t) = read () in
    if elem_lt min x then ()
    else (
      insert x;
      ())
  else (
    insert x;
    write x;
    ())

let[@assertRty] minset_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
