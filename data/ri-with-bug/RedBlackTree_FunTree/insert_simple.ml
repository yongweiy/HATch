let insert (new_node : Node.t) (tree : NodeTree.t) : NodeTree.t =
  let (new_value : Elem.t) = getValue new_node in
  let (is_leaf_res : bool) = is_leaf tree in

  if is_leaf_res then
    let (leaf : NodeTree.t) = tree in
    let (result : NodeTree.t) = mk_tree new_node leaf leaf in
    result
  else
    let (root_node : Node.t) = node tree in
    let (root_value : Elem.t) = getValue root_node in
    let (cmp : bool) = elem_lt new_value root_value in
    if cmp then
      let (left_tree : NodeTree.t) = left tree in
      let (right_tree : NodeTree.t) = right tree in
      let (new_left : NodeTree.t) = mk_tree new_node left_tree left_tree in
      let (result : NodeTree.t) = mk_tree root_node new_left right_tree in
      result
    else
      let (left_tree : NodeTree.t) = left tree in
      let (right_tree : NodeTree.t) = right tree in
      let (new_right : NodeTree.t) = mk_tree new_node right_tree right_tree in
      let (result : NodeTree.t) = mk_tree root_node left_tree new_right in
      result

let[@assertRty] insert ?l:(new_node = (true : [%v: Node.t]))
    ?l:(tree = (true : [%v: NodeTree.t])) =
  {
    ret = (true : [%v: NodeTree.t]);
    eff = Constrain ((), ());
  }
