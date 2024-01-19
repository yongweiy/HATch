let[@libRty] write ?l:(idx = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Write ((idx [@d]), v, true);
  }

let[@libRty] read ((a : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = writtenP a;
      res = (v == a : [%v: int]);
      newadding = lastL && Read (x_0, v, v == a);
    };
  |]

let[@libRty] isWritten ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = _F (Write (x_0, v, true));
      res = (v : [%v: bool]);
      newadding = lastL && IsWritten (x_0, v, v);
    };
    {
      pre = not (_F (Write (x_0, v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsWritten (x_0, v, not v);
    };
  |]
