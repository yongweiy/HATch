let is_reachable (st : Node.t) (en : Node.t) : bool =
  if isNode st then
    if isNode en then true
    else false
  else false

let[@assertRty] is_reachable ((s1 : Node.t) [@ghost]) ((s2 : Node.t) [@ghost])
     ?l:(st = (true : [%v: Node.t])) ?l:(en = (true : [%v: Node.t])) =
  { pre = rI s1 s2; res = (true : [%v: bool]); post = rI s1 s2 }
