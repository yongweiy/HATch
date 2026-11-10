let[@libRty] create ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Set.t]);
    newadding = lastL && Create (x_0, v, true);
  }

let[@libRty] add ?l:(elem = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Add ((elem [@d]), (s [@d]), v, true);
  }

let[@libRty] mem ?l:(elem = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre = _F (Add ((elem [@d]), (s [@d]), u, true));
      res = (v : [%v: bool]);
      newadding = lastL && Mem ((elem [@d]), (s [@d]), v, v);
    };
    {
      pre = not (_F (Add ((elem [@d]), (s [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && Mem ((elem [@d]), (s [@d]), v, not v);
    };
  |]

let[@libRty] isEmpty ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre = _G (not (Add (x_0, (s [@d]), u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((s [@d]), v, v);
    };
    {
      pre = _F (Add (x_0, (s [@d]), u, true));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((s [@d]), v, not v);
    };
  |]

let[@libRty] getIter ?l:(s = (true : [%v: Set.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Iter.t]);
    newadding = lastL && GetIter ((s [@d]), v, true);
  }

let[@libRty] hasIter ?l:(iter = (true : [%v: Iter.t])) ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre = _F (Add (x_0, (s [@d]), u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasIter ((iter [@d]), (s [@d]), v, v);
    };
    {
      pre = not (_F (Add (x_0, (s [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasIter ((iter [@d]), (s [@d]), v, not v);
    };
  |]

let[@libRty] hasNext ?l:(iter = (true : [%v: Iter.t])) =
  [|
    {
      pre = _G (Any true);
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((iter [@d]), v, v);
    };
    {
      pre = _G (Any false);
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((iter [@d]), v, not v);
    };
  |]

let[@libRty] next ?l:(iter = (true : [%v: Iter.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Elem.t]);
    newadding = lastL && Next ((iter [@d]), v, true);
  }
