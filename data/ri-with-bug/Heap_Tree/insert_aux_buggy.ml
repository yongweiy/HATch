let rec insert_aux (cur : Elem.t) (x : Elem.t) : unit =
  if elem_eq cur x then ()
  else if not (elem_lt x cur) then
    (
      addLeft cur x;
      ())
  else if hasRight cur then (
    let (right : Elem.t) = getRight cur in
    insert_aux right x;
    ())
  else (
    addRight cur x;
    ())

let[@assertRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (a : Elem.t) = (elem_lt v x : [%v: Elem.t]) in
       Constrain (HasParent (x, false), GetLeft (a, x)));
  }
