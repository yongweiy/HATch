let insert (x : CElem.t) (root : CElem.t) : CElem.t =
  let (vx : Elem.t) = elem_of x in
  let (balance : CElem.t -> CElem.t) =
   fun (node : CElem.t) ->
    if is_red node then node
    else
      let (left : CElem.t) = getLeft node in
      let (right : CElem.t) = getRight node in
      if (not (is_leaf left)) && is_red left then
        let (leftleft : CElem.t) = getLeft left in
        let (leftright : CElem.t) = getRight left in
        if (not (is_leaf leftleft)) && is_red leftleft then (
          setRight left node;
          setLeft node leftright;
          left)
        else if (not (is_leaf leftright)) && is_red leftright then (
          let (leftrightleft : CElem.t) = getLeft leftright in
          let (leftrightright : CElem.t) = getRight leftright in
          setLeft leftright left;
          setRight left leftrightleft;
          setRight leftright node;
          setLeft node leftrightright;
          leftright)
        else node
      else if (not (is_leaf right)) && is_red right then
        let (rightleft : CElem.t) = getLeft right in
        let (rightright : CElem.t) = getRight right in
        if (not (is_leaf rightleft)) && is_red rightleft then (
          let (rightleftleft : CElem.t) = getLeft rightleft in
          let (rightleftright : CElem.t) = getRight rightleft in
          setRight rightleft right;
          setLeft right rightleftleft;
          setLeft rightleft node;
          setRight node rightleftright;
          rightleft)
        else if (not (is_leaf rightright)) && is_red rightright then (
          setLeft right node;
          setRight node rightleft;
          right)
        else node
      else node
  in
  let rec ins : CElem.t -> CElem.t =
   fun (node : CElem.t) ->
    if is_leaf node then x
    else
      let (vl : Elem.t) = elem_of node in
      if elem_lt vx vl then (
        let (leftChild : CElem.t) = getLeft node in
        let (newLeft : CElem.t) = ins leftChild in
        setLeft node newLeft;
        let (newNode : CElem.t) = balance node in
        newNode)
      else if not (elem_lt vl vx) then (
        let (rightChild : CElem.t) = getRight node in
        let (newRight : CElem.t) = ins rightChild in
        setRight node newRight;
        let (newNode : CElem.t) = balance node in
        newNode)
      else node
  in
  let (newRoot : CElem.t) = ins root in
  newRoot
  
(*   if is_leaf root then x
  else
    let (v1 : Elem.t) = elem_of root in
    if elem_lt vx v1 then 
      let (r1 : CElem.t) = getLeft root in
      let (v2 : Elem.t) = elem_of r1 in
      if elem_eq vx v2 then
        setLeft r1 x;
        let (r1' : CElem.t) = balance r1 in
        setLeft root r1';
        let (root' : CElem.t) = balance root in
        root'
    else root (* dummy path *)
 *)
let[@assertRty] insert ?l:(x = (true : [%v: CElem.t]))
    ?l:(root = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: CElem.t]);
    eff =
      (let (nil : CElem.t) = (is_leaf v : [%v: CElem.t]) in
       let (l : CElem.t) = (not (is_leaf v) : [%v: CElem.t]) in
       let (r : CElem.t) = (not (is_leaf v) : [%v: CElem.t]) in
       Constrain
         ( (GetLeft (x, nil);
            GetRight (x, nil)),
           (GetLeft (x, l);
            GetRight (x, r)) ));
  }
(* let[@assertRty] insert ?l:(x = (is_red v : [%v: CElem.t])) *)
(*     ?l:(root = (not (is_red v) : [%v: CElem.t])) = *)
(*   { *)
(*     ret = (true : [%v: CElem.t]); *)
(*     eff = *)
(*       (let (l1 : CElem.t) = (not (v == root) : [%v: CElem.t]) in *)
(*        let (r1 : CElem.t) = (not (v == root) && not (v == l1) : [%v: CElem.t]) in *)
(*        let (r2 : CElem.t) = (not (v == root) && not (v == l1) && not (v == r1) : [%v: CElem.t]) in *)
(*        let (r3 : CElem.t) = (not (v == root) && not (v == l1) && not (v == r1) && not (v == r2) : [%v: CElem.t]) in *)
(*        Constrain *)
(*          ( (), *)
(*            ( *)
(*              IsExtern (x, true); *)
(*             GetLeft (root, l1); *)
(*             IsExtern (l1, true); *)
(*             GetRight (root, r1); *)
(*             GetRight (r1, r2); *)
(*             GetRight (r2, r3); *)
(*             IsExtern (r3, true) *)
(*           ) )); *)
(*   } *)
