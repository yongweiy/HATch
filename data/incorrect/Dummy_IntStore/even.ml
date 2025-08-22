let test (u : unit) : unit =
  let (x : int) = read () in
  (* let (b : bool) = x mod 2 in *)
  if x mod 2 != 0 then
    let (_ : unit) = write (x + 2) in
    ()
  else
    let (_ : unit) = write (x / 2) in
    ()

let[@assertRty] test ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (m : int) = (v mod 2 == 0 : [%v: int]) in
       let (n : int) = (v mod 2 == 0 : [%v: int]) in
       Constrain (Read ((), m), Read ((), n)));
  }
