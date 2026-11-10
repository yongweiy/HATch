let[@libRty] addEvent ?l:(typ = (true : [%v: int])) ?l:(target = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddEvent ((typ [@d]), (target [@d]), v, true);
  }

let[@libRty] hasNextEvent ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = _F (AddEvent (x_0, x_1, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasNextEvent (x_0, v, v);
    };
    {
      pre = not (_F (AddEvent (x_0, x_1, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNextEvent (x_0, v, not v);
    };
  |]

let[@libRty] getEventType ((typ : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = _F (AddEvent ((typ [@d]), x_1, u, true));
    res = (v == typ : [%v: int]);
    newadding = lastL && GetEventType (x_0, v, v == typ);
  }

let[@libRty] getEventTarget ((target : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = _F (AddEvent (x_0, (target [@d]), u, true));
    res = (v == target : [%v: Elem.t]);
    newadding = lastL && GetEventTarget (x_0, v, v == target);
  }

let[@libRty] nextEvent ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && NextEvent (x_0, v, true);
  }

let[@libRty] putOldElem ?l:(elem = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutOldElem ((elem [@d]), v, true);
  }

let[@libRty] hasOldElem ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = _F (PutOldElem (x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasOldElem (x_0, v, v);
    };
    {
      pre = not (_F (PutOldElem (x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasOldElem (x_0, v, not v);
    };
  |]

let[@libRty] getOldElem ((elem : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = _F (PutOldElem ((elem [@d]), u, true));
    res = (v == elem : [%v: Elem.t]);
    newadding = lastL && GetOldElem (x_0, v, v == elem);
  }

let[@libRty] putOldSize ?l:(size = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutOldSize ((size [@d]), v, true);
  }

let[@libRty] getOldSize ((size : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = _F (PutOldSize ((size [@d]), u, true));
    res = (v == size : [%v: int]);
    newadding = lastL && GetOldSize (x_0, v, v == size);
  }

let[@libRty] putSize ?l:(elem = (true : [%v: Elem.t])) ?l:(size = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutSize ((elem [@d]), (size [@d]), v, true);
  }

let[@libRty] getSize ((size : int) [@ghost]) ?l:(elem = (true : [%v: Elem.t])) =
  {
    pre = _F (PutSize ((elem [@d]), (size [@d]), u, true));
    res = (v == size : [%v: int]);
    newadding = lastL && GetSize ((elem [@d]), v, v == size);
  }
