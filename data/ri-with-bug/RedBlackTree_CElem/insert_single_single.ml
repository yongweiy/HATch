let insert (x : CElem.t) (root : CElem.t) : CElem.t =
  let (left : CElem.t) = getLeft root in
  setRight left x;
  let (leftright : CElem.t) = getRight left in
  let (leftrightleft : CElem.t) = getLeft leftright in
  let (leftrightright : CElem.t) = getRight leftright in
  setLeft leftright left;
  setRight left leftrightleft;
  setRight leftright root;
  setLeft root leftrightright;
  leftright

let[@assertRty] insert ?l:(x = (true : [%v: CElem.t]))
    ?l:(root = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: CElem.t]);
    eff =
      let (nil : CElem.t) = (is_leaf v : [%v: CElem.t]) in
      let (l : CElem.t) = (not (is_leaf v) : [%v: CElem.t]) in
      let (r : CElem.t) = (not (is_leaf v) : [%v: CElem.t]) in
      Constrain
        (
          (GetLeft (x, nil);
          GetRight (x, nil))
          ,
          (GetLeft (x, l);
           GetRight (x, r)) );
  }
