let populate (n: int) : unit =
  let rec loop : int -> unit =
    fun (i: int) ->
    if i > n then ()
    else if i == 100 then (
      put (i + 2) (i * i);
      loop (i + 1))
    else (
      put i (i * i);
      loop (i + 1))
  in
  loop 0

let[@assertRty] populate ((k1 : int) [@ghost]) ((k2 : int) [@ghost])
     ?l:(n = ((k1 < k2) : [%v: int])) =
  { pre = _G (not (Put (k, v, u, true)));
    res = (true : [%v: unit]);
    post = rI k1 k2
  }
