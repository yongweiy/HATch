let rec write_chars (q : Queue.t) (s : Stream.t) : unit =
  if isEmpty q then ()
  else
    let (c : Char.t) = take q in
    putChar s c;
    write_chars q s;
    ()

let[@assertRty] write_chars ?l:(q = (true : [%v: Queue.t]))
    ?l:(s = (true : [%v: Stream.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (h : Char.t) = (true : [%v: Char.t]) in
       let (i : Char.t) = (not (v == h) : [%v: Char.t]) in
       let (e : Char.t) = (true : [%v: Char.t]) in
       let (l : Char.t) = (true : [%v: Char.t]) in
       let (o : Char.t) = (true : [%v: Char.t]) in
       Constrain
         ( AtEOS (s, true),
           (GetChar (s, h);
            GetChar (s, e);
            GetChar (s, l);
            GetChar (s, l);
            GetChar (s, o)) ));
  }

(* let write_chars (u : unit) : unit = *)
(*   let (c : Char.t) = take () in *)
(*   putChar c; *)
(*   () *)

(* let[@assertRty] write_chars ?l:(u = (true : [%v: unit])) = *)
(*   { *)
(*     ret = (true : [%v: unit]); *)
(*     eff = *)
(*       (let (h : Char.t) = (true : [%v: Char.t]) in *)
(*        Constrain *)
(*          ( (AtEOS ((), true); *)
(*             IsEmpty ((), false)), *)
(*            (IsEmpty ((), true); *)
(*             GetChar ((), h)) )); *)
(*   } *)
