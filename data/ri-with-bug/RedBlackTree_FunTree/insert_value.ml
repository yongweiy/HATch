let insert (newnode : Node.t) (tree0 : NodeTree.t) : int =
  let (newval : Elem.t) = getValue newnode in
  let (tree : NodeTree.t) = mk_tree newnode tree0 tree0 in
  if is_leaf tree then 1
  else
    let (curnode : Node.t) = node tree in
    let (curval : Elem.t) = getValue curnode in
    if elem_eq newval curval then 2
    else 3

let[@assertRty] insert ?l:(newnode = (true : [%v: Node.t]))
    ?l:(tree0 = (true : [%v: NodeTree.t])) =
  {
    ret = (v == 2 : [%v: int]);
    eff = Constrain ((), ());
  }
