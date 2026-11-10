let insert (new_node : Node.t) (tree : NodeTree.t) : NodeTree.t =
  let (is_leaf_res : bool) = is_leaf tree in
  if is_leaf_res then
    let (leaf : NodeTree.t) = tree in
    let (result : NodeTree.t) = mk_tree new_node leaf leaf in
    result
  else tree
