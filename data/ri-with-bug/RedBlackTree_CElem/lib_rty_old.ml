let[@libRty] setLeft ?l:(parent = (true : [%v: CElem.t]))
    ?l:(child = (true : [%v: CElem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetLeft ((parent [@d]), (child [@d]), v, true);
  }

let[@libRty] getLeft ((child : CElem.t) [@ghost])
    ?l:(parent = (true : [%v: CElem.t])) =
  {
    pre =
      _F
        (SetLeft ((parent [@d]), (child [@d]), u, true)
        && _X (_G (not (SetLeft ((parent [@d]), a, u, true)))));
    res = (v == child : [%v: CElem.t]);
    newadding = lastL && GetLeft ((parent [@d]), v, v == child);
  }

let[@libRty] setRight ?l:(parent = (true : [%v: CElem.t]))
    ?l:(child = (true : [%v: CElem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetRight ((parent [@d]), (child [@d]), v, true);
  }

let[@libRty] getRight ((child : CElem.t) [@ghost])
    ?l:(parent = (true : [%v: CElem.t])) =
  {
    pre =
      _F
        (SetRight ((parent [@d]), (child [@d]), u, true)
        && _X (_G (not (SetRight ((parent [@d]), a, u, true)))));
    res = (v == child : [%v: CElem.t]);
    newadding = lastL && GetRight ((parent [@d]), v, v == child);
  }
