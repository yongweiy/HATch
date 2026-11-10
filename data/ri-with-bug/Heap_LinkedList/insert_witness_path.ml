(* Simplified single-path client program from infer-incorrectness witness

   This removes all branching and path conditions, executing only the
   exact sequence of operations from the witness.

   Witness execution trace:
   1. hasHead() -> true
   2. getHead() -> hd_0
   3. hasNext(hd_0) -> true
   4. getNext(hd_0) -> next_0
   5. setHead(res_0)

   Ghost bindings from witness:
   - min where elem_lt min x
   - min' where elem_lt min' min
   - res_0 == min'
   - hd_0 should equal min initially

   The query asks: Can head change from min to min' where min' < min?
*)

let insert_witness_path (x : Elem.t) : unit =
  (* Just execute the exact operation sequence, no branches *)
  let (_b1 : bool) = hasHead () in
  let (hd : Elem.t) = getHead () in
  let (_b2 : bool) = hasNext hd in
  let (next : Elem.t) = getNext hd in
  (* The witness shows setHead is called with res_0 == min'
     In the buggy implementation, this could be 'next' or some other value
     that violates the heap property *)
  setHead next;
  ()

(* Same query as original *)
let[@assertRty] insert_witness_path ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (min : Elem.t) = (elem_lt v x : [%v: Elem.t]) in
       let (min' : Elem.t) = (elem_lt min v : [%v: Elem.t]) in
       Constrain (GetHead ((), min), GetHead ((), min')));
  }
