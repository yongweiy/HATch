let rec write_chars (u : unit) : unit =
  if isEmpty () then ()
  else
    let (c : Char.t) = take () in
    putChar c;
    write_chars ();
    ()

let[@assertRty] write_chars ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (c1 : Char.t) = (true : [%v: Char.t]) in
       let (c2 : Char.t) = (not (v == c1) : [%v: Char.t]) in
       Constrain
         ( (Take ((), c1);
            AtEOS ((), true)),
           GetChar ((), c2) ));
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
