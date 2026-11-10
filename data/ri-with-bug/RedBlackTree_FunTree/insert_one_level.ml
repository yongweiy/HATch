let insert (new_node : Node.t) (tree : NodeTree.t) : NodeTree.t =
  let (new_value : Elem.t) = getValue new_node in
  let (is_leaf_res : bool) = is_leaf tree in

  if is_leaf_res then
    let (leaf : NodeTree.t) = tree in
    let (result : NodeTree.t) = mk_tree new_node leaf leaf in
    result
  else
    let (root_node : Node.t) = node tree in
    let (left_tree : NodeTree.t) = left tree in
    let (right_tree : NodeTree.t) = right tree in
    let (new_left : NodeTree.t) = mk_tree new_node left_tree left_tree in
    let (result : NodeTree.t) = mk_tree root_node new_left right_tree in
    result
