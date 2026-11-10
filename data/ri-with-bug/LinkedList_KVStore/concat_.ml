let concat (xs : Ptr.t) (ys : Ptr.t) : Ptr.t =
  let rec aux : Ptr.t -> Ptr.t =
   fun (curr : Ptr.t) ->
    if is_nullptr curr then ys
    else
      let (next : Ptr.t) = getNext curr in
      let (ys' : Ptr.t) = aux next in
      putNext curr ys';
      curr
  in
  let (res : Ptr.t) = aux xs in
  res

let[@assertRty] concat ?l:(xs = (not (is_nullptr v) : [%v: Ptr.t]))
    ?l:(ys = (not (is_nullptr v) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      (let (v1 : Elem.t) = (true : [%v: Elem.t]) in
       let (v2 : Elem.t) = (not (v1 == v2) : [%v: Elem.t]) in
       Constrain (GetVal (ys, v1), GetVal (ys, v2)));
  }
