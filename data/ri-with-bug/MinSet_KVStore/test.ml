let rec test (x : Elem.t) : unit =
  if isWritten () then
    if hasValue x then ()
    else
      let (k : Key.t) = randomKey () in
      if exists k then (
        minset_insert x;
        ())
      else
        let (min : Elem.t) = read () in
        if elem_lt min x then ()
        else (
          put k x;
          ())
  else ()

let[@assertRty] test ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
