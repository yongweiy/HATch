let insert (x : Ptr.t) (root : Ptr.t) : Ptr.t =
  let (vx : Elem.t) = getValue x in
  let (isRed : Ptr.t -> bool) =
   fun (node : Ptr.t) ->
    if is_nullptr node then false
    else
      let (ans : bool) = getColor node in
      ans
  in
  let (balance : Ptr.t -> Ptr.t) =
   fun (node : Ptr.t) ->
    let (nodeIsRed : bool) = getColor node in
    if nodeIsRed then node
    else
      let (left : Ptr.t) = getLeft node in
      let (leftIsRed : bool) = isRed left in
      let (right : Ptr.t) = getRight node in
      let (rightIsRed : bool) = isRed right in
      if leftIsRed then
        let (leftleft : Ptr.t) = getLeft left in
        let (leftleftIsRed : bool) = isRed leftleft in
        let (leftright : Ptr.t) = getRight left in
        let (leftrightIsRed : bool) = isRed leftright in
        if leftleftIsRed then (
          setRight left node;
          setLeft node leftright;
          setColor leftleft false;
          left)
        else if leftrightIsRed then (
          let (leftrightleft : Ptr.t) = getLeft leftright in
          let (leftrightright : Ptr.t) = getRight leftright in
          setLeft leftright left;
          setRight left leftrightleft;
          setRight leftright node;
          setLeft node leftrightright;
          setColor left false;
          leftright)
        else node
      else if rightIsRed then node (* FIXME *)
      else node
  in

  let rec ins : Ptr.t -> Ptr.t =
   fun (node : Ptr.t) ->
    if is_nullptr node then x
    else
      let (vl : Elem.t) = getValue node in
      if elem_lt vx vl then (
        let (leftChild : Ptr.t) = getLeft node in
        let (newLeft : Ptr.t) = ins leftChild in
        setLeft node newLeft;
        let (newNode : Ptr.t) = balance node in
        newNode)
      (* else if not (elem_lt vl vx) then ( *)
      (*   let (rightChild : Ptr.t) = getRight node in *)
      (*   let (newRight : Ptr.t) = ins rightChild in *)
      (*   setRight node newRight; *)
      (*   let (newNode : Ptr.t) = balance node in *)
      (*   newNode) *)
      else node (* element already exists *)
  in

  let (newRoot : Ptr.t) = ins root in
  newRoot
(* let (left : Ptr.t) = getLeft root in *)
(* setRight left x; *)
(* let (root' : Ptr.t) = balance root in *)
(* root' *)

let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t]))
    ?l:(root = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      (let (nil : Ptr.t) = (is_nullptr v : [%v: Ptr.t]) in
       let (l : Ptr.t) = ((not (is_nullptr v)) && not (v == x) : [%v: Ptr.t]) in
       let (r : Ptr.t) = ((not (is_nullptr v)) && not (v == x) : [%v: Ptr.t]) in
       Constrain
         ( (GetLeft (x, nil);
            GetRight (x, nil)),
           (GetLeft (x, l);
            GetRight (x, r)) ));
  }

(* let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t])) *)
(*     ?l:(root = (true : [%v: Ptr.t])) = *)
(*   { *)
(*     ret = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (what : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        Constrain (GetColor (what, true), GetColor (what, false))); *)
(*   } *)
(* let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t])) *)
(*     ?l:(root = (not (v == x) : [%v: Ptr.t])) = *)
(*   { *)
(*     ret = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (l1 : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        let (r1 : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        let (r2 : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        let (r3 : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        Constrain *)
(*          ( (GetColor (root, false); *)
(*             IsLeaf (x, true)), *)
(*            (GetLeft (root, l1); *)
(*             IsLeaf (l1, true); *)
(*             GetRight (root, r1); *)
(*             GetRight (r1, r2); *)
(*             GetRight (r2, r3); *)
(*             IsLeaf (r3, true)) )); *)
(*   } *)
