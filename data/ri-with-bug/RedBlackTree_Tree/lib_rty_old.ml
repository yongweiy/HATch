let[@libRty] createPtr ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Ptr.t]);
    newadding = lastL && CreatePtr (x_0, v, true);
  }

let[@libRty] isLeaf ?l:(p = (true : [%v: Ptr.t])) =
  [|
    {
      pre = _G (not (SetLeft ((p [@d]), x_0, u, true) || SetRight ((p [@d]), x_0, u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && IsLeaf ((p [@d]), v, v);
    };
    {
      pre = _F (SetLeft ((p [@d]), x_0, u, true) || SetRight ((p [@d]), x_0, u, true));
      res = (not v : [%v: bool]);
      newadding = lastL && IsLeaf ((p [@d]), v, not v);
    };
  |]

let[@libRty] setValue ?l:(p = (true : [%v: Ptr.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetValue ((p [@d]), (a [@d]), v, true);
  }

let[@libRty] getValue ((a : Elem.t) [@ghost]) ?l:(p = (true : [%v: Ptr.t])) =
  {
    pre = _F (SetValue ((p [@d]), (a [@d]), u, true));
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetValue ((p [@d]), v, v == a);
  }

let[@libRty] setColor ?l:(p = (true : [%v: Ptr.t])) ?l:(c = (true : [%v: bool])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetColor ((p [@d]), (c [@d]), v, true);
  }

let[@libRty] getColor ((c : bool) [@ghost]) ?l:(p = (true : [%v: Ptr.t])) =
  {
    pre = _F (SetColor ((p [@d]), (c [@d]), u, true));
    res = (v == c : [%v: bool]);
    newadding = lastL && GetColor ((p [@d]), v, v == c);
  }

let[@libRty] setLeft ?l:(p = (true : [%v: Ptr.t])) ?l:(left = (true : [%v: Ptr.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetLeft ((p [@d]), (left [@d]), v, true);
  }

let[@libRty] getLeft ((left : Ptr.t) [@ghost]) ?l:(p = (true : [%v: Ptr.t])) =
  {
    pre = _F (SetLeft ((p [@d]), (left [@d]), u, true));
    res = (v == left : [%v: Ptr.t]);
    newadding = lastL && GetLeft ((p [@d]), v, v == left);
  }

let[@libRty] setRight ?l:(p = (true : [%v: Ptr.t])) ?l:(right = (true : [%v: Ptr.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetRight ((p [@d]), (right [@d]), v, true);
  }

let[@libRty] getRight ((right : Ptr.t) [@ghost]) ?l:(p = (true : [%v: Ptr.t])) =
  {
    pre = _F (SetRight ((p [@d]), (right [@d]), u, true));
    res = (v == right : [%v: Ptr.t]);
    newadding = lastL && GetRight ((p [@d]), v, v == right);
  }

let[@libRty] hasLeft ?l:(p = (true : [%v: Ptr.t])) =
  [|
    {
      pre = _F (SetLeft ((p [@d]), x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasLeft ((p [@d]), v, v);
    };
    {
      pre = not (_F (SetLeft ((p [@d]), x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasLeft ((p [@d]), v, not v);
    };
  |]

let[@libRty] hasRight ?l:(p = (true : [%v: Ptr.t])) =
  [|
    {
      pre = _F (SetRight ((p [@d]), x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasRight ((p [@d]), v, v);
    };
    {
      pre = not (_F (SetRight ((p [@d]), x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasRight ((p [@d]), v, not v);
    };
  |]
