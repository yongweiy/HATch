let is_edge (st : Node.t) (en : Node.t) : bool =
  if existsE st en then true else false

let[@assertRty] is_edge ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
    ((c : Color.t) [@ghost]) ?l:(st = (true : [%v: Node.t]))
    ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 s2 c; res = (true : [%v: bool]); post = rI s1 s2 c }
