let insert (x : Ptr.t) (root : Ptr.t) : Ptr.t =
  let (isRed : Ptr.t -> bool) =
   fun (node : Ptr.t) ->
    if is_nullptr node then false
    else
      let (ans : bool) = getColor node in
      ans
  in
  let (balance : Ptr.t -> Ptr.t) =
   fun (node : Ptr.t) ->
    if isRed node then node
    else
      let (sho : Ptr.t) = getLeft node in
      let (left : Ptr.t) = getLeft node in
      let (right : Ptr.t) = getRight node in
      if isRed left then
        let (leftleft : Ptr.t) = getLeft left in
        let (leftright : Ptr.t) = getRight left in
        if isRed leftleft then (
          setRight left node;
          setLeft node leftright;
          setColor leftleft false;
          left)
        else if isRed leftright then (
          let (leftrightleft : Ptr.t) = getLeft leftright in
          let (leftrightright : Ptr.t) = getRight leftright in
          setColor left false;
          setLeft leftright left;
          setRight left leftrightleft;
          setRight leftright node;
          setLeft node leftrightright;
          leftright)
        else node
      else node
  in
  let (left : Ptr.t) = getLeft root in
  setRight left x;
  let (leftright : Ptr.t) = getRight left in
  let (leftrightleft : Ptr.t) = getLeft leftright in
  let (leftrightright : Ptr.t) = getRight leftright in
  setColor left false;
  setLeft leftright left;
  setRight left leftrightleft;
  setRight leftright root;
  setLeft root leftrightright;
  leftright

let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t]))
    ?l:(root = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      let (nil : Ptr.t) = (is_nullptr v : [%v: Ptr.t]) in
      let (l : Ptr.t) = (not (is_nullptr v) : [%v: Ptr.t]) in
      let (r : Ptr.t) = (not (is_nullptr v) : [%v: Ptr.t]) in
      Constrain
        (
          (GetLeft (x, nil);
          GetRight (x, nil))
          ,
          (GetLeft (x, l);
           GetRight (x, r)) );
  }
