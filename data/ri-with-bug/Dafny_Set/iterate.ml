let copy (it : Iter.t) : Set.t =
  let (res : Set.t) = create () in
  let rec loop : Elem.t -> unit =
   fun (max : Elem.t) ->
    if hasNext it then
      let (a : Elem.t) = next it in
      if elem_lt max a then (
        add a res;
        loop a;
        ())
  in
  if hasNext it then (
    let (init : Elem.t) = next it in
    add init res;
    loop init;
    res)
  else res

let[@assertRty] copy ?l:(it = (true : [%v: Iter.t])) =
  {
    ret = (true : [%v: Set.t]);
    eff =
      (let (v1 : Elem.t) = (true : [%v: Elem.t]) in
       let (v2 : Elem.t) = (true : [%v: Elem.t]) in
       Constrain
         ( (),
           (Mem (v1, ret, true);
            Mem (v2, ret, true)) ));
  }
(* let[@assertRty] copy ?l:(it1 = (true : [%v: Iter.t])) *)
(*     ?l:(s2 = (true : [%v: Set.t])) = *)
(*   { *)
(*     ret = (true : [%v: unit]); *)
(*     eff = *)
(*       (let (s1 : Set.t) = (true : [%v: Set.t]) in *)
(*        let (vl : Elem.t) = (true : [%v: Elem.t]) in *)
(*        Constrain *)
(*          ( (HasIter (it1, s1, true); *)
(*             IsEmpty (s2, true)), *)
(*            (Mem (vl, s1, true); *)
(*             Mem (vl, s2, false)) )); *)
(* } *)
