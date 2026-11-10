let[@libRty] create ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Queue.t]);
    newadding = lastL && Create (x_0, v, true);
  }

let[@libRty] isEmpty ?l:(q = (true : [%v: Queue.t])) =
  [|
    {
      pre = _G (not (Add (x_0, (q [@d]), u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, v);
    };
    {
      pre = _F (Add (x_0, (q [@d]), u, true));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, not v);
    };
  |]

let[@libRty] add ?l:(node = (true : [%v: Node.t])) ?l:(q = (true : [%v: Queue.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Add ((node [@d]), (q [@d]), v, true);
  }

let[@libRty] take ((node : Node.t) [@ghost]) ?l:(q = (true : [%v: Queue.t])) =
  {
    pre = _F (Add ((node [@d]), (q [@d]), u, true));
    res = (v == node : [%v: Node.t]);
    newadding = lastL && Take ((q [@d]), v, v == node);
  }

let[@libRty] connect ?l:(n1 = (true : [%v: Node.t])) ?l:(n2 = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Connect ((n1 [@d]), (n2 [@d]), v, true);
  }

let[@libRty] isConnected ?l:(n1 = (true : [%v: Node.t])) ?l:(n2 = (true : [%v: Node.t])) =
  [|
    {
      pre = _F (Connect ((n1 [@d]), (n2 [@d]), u, true));
      res = (v : [%v: bool]);
      newadding = lastL && IsConnected ((n1 [@d]), (n2 [@d]), v, v);
    };
    {
      pre = not (_F (Connect ((n1 [@d]), (n2 [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsConnected ((n1 [@d]), (n2 [@d]), v, not v);
    };
  |]

let[@libRty] getNeighbors ?l:(node = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Iterator.t]);
    newadding = lastL && GetNeighbors ((node [@d]), v, true);
  }

let[@libRty] hasNext ?l:(node = (true : [%v: Node.t])) ?l:(iter = (true : [%v: Iterator.t])) =
  [|
    {
      pre = _F (Connect ((node [@d]), x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((node [@d]), (iter [@d]), v, v);
    };
    {
      pre = not (_F (Connect ((node [@d]), x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((node [@d]), (iter [@d]), v, not v);
    };
  |]

let[@libRty] next ?l:(node = (true : [%v: Node.t])) ?l:(iter = (true : [%v: Iterator.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Node.t]);
    newadding = lastL && Next ((node [@d]), (iter [@d]), v, true);
  }

let[@libRty] initVisited ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && InitVisited (x_0, v, true);
  }

let[@libRty] markVisited ?l:(node = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && MarkVisited ((node [@d]), v, true);
  }

let[@libRty] isVisited ?l:(node = (true : [%v: Node.t])) =
  [|
    {
      pre = _F (MarkVisited ((node [@d]), u, true));
      res = (v : [%v: bool]);
      newadding = lastL && IsVisited ((node [@d]), v, v);
    };
    {
      pre = not (_F (MarkVisited ((node [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsVisited ((node [@d]), v, not v);
    };
  |]
