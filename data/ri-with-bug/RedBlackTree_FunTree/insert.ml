let insert (x : Node.t) (root : NodeTree.t) : NodeTree.t =
  let (balance : NodeTree.t -> NodeTree.t) =
   fun (c : NodeTree.t) ->
    let (n : Node.t) = node c in
    if getColor n then c
    else
      let (l : NodeTree.t) = left c in
      let (r : NodeTree.t) = right c in
      let (ln : Node.t) = node l in
      let (rn : Node.t) = node r in
      if getColor ln then
        let (ll : NodeTree.t) = left l in
        let (lr : NodeTree.t) = right l in
        let (lln : Node.t) = node ll in
        let (lrn : Node.t) = node lr in
        if getColor lln then (
          let (r' : NodeTree.t) = mk_tree n lr r in
          let (c' : NodeTree.t) = mk_tree ln ll r' in
          setColor lln false;
          c')
        else c
      else c
  in
  let (leaf : NodeTree.t) = mk_leaf () in
  let (vx : Elem.t) = getValue x in
  let rec ins : NodeTree.t -> NodeTree.t =
    fun (c : NodeTree.t) ->
      if is_leaf c then
        let (c' : NodeTree.t) = mk_tree x leaf leaf in
        c'
      else
        let (n : Node.t) = node c in
        let (l : NodeTree.t) = left c in
        let (r : NodeTree.t) = right c in
        let (vn : Elem.t) = getValue n in
        if elem_lt vx vn then (
          let (l' : NodeTree.t) = ins l in
          let (c' : NodeTree.t) = mk_tree n l' r in
          let (c'' : NodeTree.t) = balance c' in
          c''
        ) else if not (elem_lt vn vx) then (
          let (r' : NodeTree.t) = ins r in
          let (c' : NodeTree.t) = mk_tree n l r' in
          let (c'' : NodeTree.t) = balance c' in
          c''
        ) else c
  in
  (* let (n : Node.t) = node root in *)
  (* let (vl : Elem.t) = getValue n in *)
  (* let (l : NodeTree.t) = left root in *)
  (* let (r : NodeTree.t) = right root in *)
  (* let (ll : NodeTree.t) = left l in *)
  (* let (t : NodeTree.t) = mk_tree x leaf leaf in *)
  (* let (t' : NodeTree.t) = mk_tree x t t in *)
  (* let (root'' : NodeTree.t) = mk_tree x t' t' in *)
  (* let (root'' : NodeTree.t) = mk_tree n l t in *)
  let (root' : NodeTree.t) = ins root in
  root'

let[@assertRty] insert ?l:(x = (true : [%v: Node.t]))
    ?l:(root = (true : [%v: NodeTree.t])) =
  {
    ret = (true : [%v: NodeTree.t]);
    eff =
      (let (what : Node.t) = (true : [%v: Node.t]) in
       Constrain (GetColor (what, true), GetColor (what, false)));
  }
