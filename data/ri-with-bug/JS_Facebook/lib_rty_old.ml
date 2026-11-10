let[@libRty] setClassName ?l:(node = (true : [%v: Node.t])) ?l:(cls = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetClassName ((node [@d]), (cls [@d]), v, true);
  }

let[@libRty] getClassName ((cls : int) [@ghost]) ?l:(node = (true : [%v: Node.t])) =
  {
    pre = _F (SetClassName ((node [@d]), (cls [@d]), u, true));
    res = (v == cls : [%v: int]);
    newadding = lastL && GetClassName ((node [@d]), v, v == cls);
  }

let[@libRty] setNodeId ?l:(node = (true : [%v: Node.t])) ?l:(id = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetNodeId ((node [@d]), (id [@d]), v, true);
  }

let[@libRty] getNodeId ((id : int) [@ghost]) ?l:(node = (true : [%v: Node.t])) =
  {
    pre = _F (SetNodeId ((node [@d]), (id [@d]), u, true));
    res = (v == id : [%v: int]);
    newadding = lastL && GetNodeId ((node [@d]), v, v == id);
  }

let[@libRty] addChild ?l:(parent = (true : [%v: Node.t])) ?l:(child = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddChild ((parent [@d]), (child [@d]), v, true);
  }

let[@libRty] getChildren ?l:(node = (true : [%v: Node.t])) =
  {
    pre = not (_F (GetChildren ((node [@d]), it, true)));
    res = (true : [%v: Iterator.t]);
    newadding = lastL && GetChildren ((node [@d]), v, true);
  }

let[@libRty] findByClass ?l:(iter = (true : [%v: Iterator.t])) ?l:(cls = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Node.t]);
    newadding = lastL && FindByClass ((iter [@d]), (cls [@d]), v, true);
  }

let[@libRty] hasNext ((child : Node.t) [@ghost]) ?l:(node = (true : [%v: Node.t])) ?l:(iter = (true : [%v: Iterator.t])) =
  [|
    {
      pre =
        _F
          (AddChild ((node [@d]), (child [@d]), u, true)
          && _X
               (_F
                  (GetChildren ((node [@d]), (iter [@d]), true)
                  && _X
                       (not
                          (_F
                             (Next
                                ((node [@d]), (iter [@d]), (child [@d]), true)))))));
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((node [@d]), (iter [@d]), v, v);
    };
    {
      pre =
        _U
          (not (AddChild ((node [@d]), child, u, true)))
          (GetChildren ((node [@d]), (iter [@d]), true));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((node [@d]), (iter [@d]), v, not v);
    };
  |]

let[@libRty] next ?l:(node = (true : [%v: Node.t])) ?l:(iter = (true : [%v: Iterator.t])) =
  {
    pre =
      _F
        (AddChild ((node [@d]), v, u, true)
        && _X
             (_F
                (GetChildren ((node [@d]), (iter [@d]), true)
                && _X
                     (not (_F (Next ((node [@d]), (iter [@d]), v, true)))))));
    res = (true : [%v: Node.t]);
    newadding = lastL && Next ((node [@d]), (iter [@d]), v, true);
  }

let[@libRty] putContact ?l:(id = (true : [%v: int])) ?l:(contact = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutContact ((id [@d]), (contact [@d]), v, true);
  }

let[@libRty] getContact ((contact : int) [@ghost]) ?l:(id = (true : [%v: int])) =
  {
    pre = _F (PutContact ((id [@d]), (contact [@d]), u, true));
    res = (v == contact : [%v: int]);
    newadding = lastL && GetContact ((id [@d]), v, v == contact);
  }

let[@libRty] memContact ?l:(id = (true : [%v: int])) =
  [|
    {
      pre = _F (PutContact ((id [@d]), x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && MemContact ((id [@d]), v, v);
    };
    {
      pre = not (_F (PutContact ((id [@d]), x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && MemContact ((id [@d]), v, not v);
    };
  |]
