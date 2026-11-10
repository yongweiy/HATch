let rec insert (x : Elem.t) : unit =
  (* if hasValue x then () *)
  (* else *)
  let (k : Key.t) = randomKey () in
  if exists k then (
    insert x;
    ())
  else (
    put k x;
    ())

(* let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) = *)
(*   { *)
(*     ret = (true : [%v: unit]); *)
(*     eff = *)
(*       (let (k : Key.t) = (true : [%v: Key.t]) in *)
(*        Constrain *)
(*          ( (), *)
(*            (Del (k, x); *)
(*             HasValue (x, true)) )); *)
(*   } *)
let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (k1 : Key.t) = (true : [%v: Key.t]) in
       let (k2 : Key.t) = (not (v == k1) : [%v: Key.t]) in
       Constrain
         ( (),
           (Get (k1, x);
            Get (k2, x)) ));
  }

(* let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) = *)
(*   { *)
(*     ret = (true : [%v: unit]); *)
(*     eff = *)
(*       (let (k1 : Key.t) = (true : [%v: Key.t]) in *)
(*        let (k2 : Key.t) = (not (v == k1) : [%v: Key.t]) in *)
(*        Constrain *)
(*          ( (), *)
(*            (Get (k1, x); *)
(*             Get (k2, x)) )); *)
(*   } *)
