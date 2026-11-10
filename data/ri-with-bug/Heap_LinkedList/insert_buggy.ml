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
(*
   inferred:
(x:{v:Elem.t | true}) → (ret:{v:unit | true})!min ← {v:Elem.t | elem_lt v x}; min' ← {v:Elem.t | ¬v == min}; x_12 ← {v:bool | true}; br_21 ← {v:unit | x_12}; hd_0 ← {v:Elem.t | true}; res_0 ← {v:Elem.t | true}; br_23 ← {v:unit | hd_0 == x}; u_1 ← {v:unit | res_0 == hd_0}; (admit(⟨setHead x_0 = vret | x_0 == min⟩;⟨setHead x_0 = vret | x_0 == hd_0 ∧ x_0 == x ∧ ¬x_0 == min⟩); (x_12 ← hasHead(()); (hd_0 ← getHead(()); () ← setHead(res_0))))
Task 1(insert): exec time 1.890218(s), type check succeeded

*)
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

(* reachable query: min not preserved because prefix gets truncated *)
let[@assertRty] insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (min : Elem.t) = (elem_lt v x : [%v: Elem.t]) in
       let (min' : Elem.t) = (elem_lt min v : [%v: Elem.t]) in
       Constrain (GetHead ((), min), GetHead ((), min')));
  }
