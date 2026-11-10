let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: Bytes.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] del ?l:(k = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Del ((k [@d]), u, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: Path.t])) =
  [|
    {
      pre = existsP k;
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, v);
    };
    {
      pre = not (existsP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, not v);
    };
  |]

let[@libRty] get ((a : Bytes.t) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre =
      storedP k a
      && _G (not (AddChild ((a [@d]), child, u, not (k == parent child))));
    res = (v == a : [%v: Bytes.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] isDir ((child : Path.t) [@ghost])
    ?l:(bytes = (true : [%v: Bytes.t])) =
  [|
    {
      pre =
        _F
          (AddChild ((bytes [@d]), (child [@d]), u, true)
          && _X (_G (not (DelChild ((bytes [@d]), (child [@d]), u, true)))));
      res = (v : [%v: bool]);
      newadding = lastL && IsDir ((bytes [@d]), v, v);
    };
    {
      pre = _G (not (AddChild ((bytes [@d]), child, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsDir ((bytes [@d]), v, not v);
    };
  |]

let[@libRty] memChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  [|
    {
      pre =
        _F
          (AddChild ((bytes [@d]), (child [@d]), u, true)
          && _X (_G (not (DelChild ((bytes [@d]), (child [@d]), u, true)))));
      res = (v : [%v: bool]);
      newadding = lastL && MemChild ((bytes [@d]), (child [@d]), v, v);
    };
    {
      pre =
        not
          (_F
             (AddChild ((bytes [@d]), (child [@d]), u, true)
             && _X (_G (not (DelChild ((bytes [@d]), (child [@d]), u, true))))));
      res = (not v : [%v: bool]);
      newadding = lastL && MemChild ((bytes [@d]), (child [@d]), v, not v);
    };
  |]

let[@libRty] addChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddChild ((bytes [@d]), (child [@d]), v, true);
  }

let[@libRty] delChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && DelChild ((bytes [@d]), (child [@d]), v, true);
  }

let[@libRty] getChildren ?l:(bytes = (true : [%v: Bytes.t])) =
  {
    pre = not (_F (GetChildren ((bytes [@d]), it, true)));
    res = (true : [%v: Iterator.t]);
    newadding = lastL && GetChildren ((bytes [@d]), v, true);
  }

let[@libRty] hasNext ((child : Path.t) [@ghost]) ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(iter = (true : [%v: Iterator.t])) =
  [|
    {
      pre =
        _F
          (AddChild ((bytes [@d]), (child [@d]), u, true)
          && _X (_G (not (DelChild ((bytes [@d]), (child [@d]), u, true))))
          && _X
               (_F
                  (GetChildren ((bytes [@d]), (iter [@d]), true)
                  && _X
                       (not
                          (_F
                             (Next
                                ((bytes [@d]), (iter [@d]), (child [@d]), true)))))));
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((bytes [@d]), (iter [@d]), v, v);
    };
    {
      pre =
        _U
          (not (AddChild ((bytes [@d]), child, u, true)))
          (GetChildren ((bytes [@d]), (iter [@d]), true));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((bytes [@d]), (iter [@d]), v, not v);
    };
  |]

let[@libRty] next ((c : Path.t) [@ghost]) ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(iter = (true : [%v: Iterator.t])) =
  {
    pre =
      _F
        (AddChild ((bytes [@d]), (c [@d]), u, true)
        && _X (_G (not (DelChild ((bytes [@d]), (c [@d]), u, true))))
        && _X
             (_F
                (GetChildren ((bytes [@d]), (iter [@d]), true)
                && _X
                     (not
                        (_F
                           (Next
                              ((bytes [@d]), (iter [@d]), (c [@d]), true)))))));
    res = (v == c : [%v: Path.t]);
    newadding = lastL && Next ((bytes [@d]), (iter [@d]), v, v == c);
  }
