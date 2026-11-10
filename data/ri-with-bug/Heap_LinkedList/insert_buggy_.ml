(* let insert (x : Elem.t) : unit = *)
(*   if hasHead () then ( *)
(*     let (hd : Elem.t) = getHead () in *)
(*     let (next : Elem.t) = getNext hd in *)
(*     setNext x next; *)
(*     setHead x; *)
(*     ()) *)
(*   else ( *)
(*     setHead x; *)
(*     ()) *)
let insert (x : Elem.t) : unit =
  let rec insert_aux : Elem.t -> Elem.t =
   fun (cur : Elem.t) ->
    if elem_eq cur x then cur
    else if elem_lt x cur then (
      setNext x cur;
      x)
    else if hasNext cur then
      let (next : Elem.t) = getNext cur in
      let (res : Elem.t) = insert_aux next in
      (* setNext cur res; *)
      res
    else (
      setNext cur x;
      cur)
  in
  if hasHead () then (
    let (hd : Elem.t) = getHead () in
    let (res : Elem.t) = insert_aux hd in
    setHead res;
    ())
  else (
    setHead x;
    ())

(* unreachable query: sortedness is preserved even though prefix gets truncated *)
let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (a : Elem.t) = (true : [%v: Elem.t]) in
       let (b : Elem.t) = (elem_lt a v : [%v: Elem.t]) in
       let (c : Elem.t) = (elem_lt v a : [%v: Elem.t]) in
       Constrain (GetNext (a, b), GetNext (a, c)));
  }
