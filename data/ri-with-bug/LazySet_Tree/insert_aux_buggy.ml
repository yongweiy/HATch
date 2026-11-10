let rec insert_aux (cur : Elem.t) (x : Elem.t) : unit =
  if elem_eq cur x then ()
  else if not (elem_lt x cur) then
    if hasLeft cur then (
      let (left : Elem.t) = getLeft cur in
      insert_aux left x;
      ())
    else (
      addLeft cur x;
      ())
  else if hasRight cur then (
    let (right : Elem.t) = getRight cur in
    insert_aux right x;
    ())
  else (
    addRight cur x;
    ())

(* Incorrectness specification: the insert_aux function can violate BST ordering
   by placing elements on wrong sides of the tree *)

let[@assertRty] insert_aux ?l:(cur = (true : [%v: Elem.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (HasLeft (cur, true);
           HasRight (cur, true)) );
  }
