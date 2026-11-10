let insert (x : CElem.t) (root : CElem.t) : CElem.t =
  let (left : CElem.t) = getLeft root in
  setLeft root x;
  let (root' : CElem.t) = mk_red root in
  root'

let[@assertRty] insert ?l:(x = (true : [%v: CElem.t]))
    ?l:(root = (true : [%v: CElem.t])) =
  {
    ret = (elem_of root == elem_of v : [%v: CElem.t]);
    eff = Constrain ((), ());
  }
