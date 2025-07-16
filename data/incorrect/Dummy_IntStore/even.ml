let test (u: unit) : unit =
  let (x : int) = read () in
  (* let (b : bool) = x mod 2 in *)
  if x mod 2 then
    write (x/2)
  else
    write (x+2)

let[@assertRty] test ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff = Reach(
        let n = (v mod 2 == 0 : [%v: int]) in
        Write(n, ()));
  }
