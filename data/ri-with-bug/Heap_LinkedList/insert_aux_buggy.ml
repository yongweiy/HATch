let rec insert_aux (cur : Elem.t) (x : Elem.t) : Elem.t =
  if elem_eq cur x then cur
  else if not (elem_lt x cur) then (
    setNext x cur;
    x)
  else if hasNext cur then
    let (next : Elem.t) = getNext cur in
    let (res : Elem.t) = insert_aux next x in
    setNext cur res;
    cur
  else (
    setNext cur x;
    cur)

(* Incorrectness specification: the insert_aux function can violate min-heap ordering
   by placing larger elements as next of smaller ones *)

let[@assertRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      (let (a : Elem.t) = (elem_lt x v : [%v: Elem.t]) in
       Constrain (HasPrev (x, false), GetNext (a, x)));
  }
