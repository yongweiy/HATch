let insert (x : Node.t) (root : NodeTree.t) : NodeTree.t =
  let (leaf : NodeTree.t) = mk_leaf () in
  (* let (t : NodeTree.t) = mk_tree x root root in *)
  (* let (t' : NodeTree.t) = mk_tree x t t in *)
  setColor x false;
  (* let (root'' : NodeTree.t) = mk_tree x t' t' in *)
  (* let (l : NodeTree.t) = left t in *)
  root

let[@assertRty] insert ?l:(x = (true : [%v: Node.t]))
    ?l:(root = (true : [%v: NodeTree.t])) =
  {
    ret = (true : [%v: NodeTree.t]);
    eff =
      (let (what : Node.t) = (true : [%v: Node.t]) in
       Constrain (GetColor (what, true), GetColor (what, false)));
  }
