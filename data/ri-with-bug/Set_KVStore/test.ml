let test (k : Key.t) (elm : Elem.t) : unit =
  let (old : Elem.t) = get k in
  if elem_eq elm old then ()
  else (
    put k elm;
    ())

(* the query is asking for the reachability of an
   output state where [k] is mapped to some
   [other] value than [elm], *)
let[@assertRty] test ?l:(k = (true : [%v: Key.t]))
    ?l:(elm = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (other : Elem.t) = (not (v == elm) : [%v: Elem.t]) in
       Constrain ((), Get (k, other)));
  }
