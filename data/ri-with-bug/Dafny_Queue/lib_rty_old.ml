let[@libRty] isEmpty ((c1 : Char.t) [@ghost]) ((c2 : Char.t) [@ghost])
    ?l:(q = (true : [%v: Queue.t])) =
  [|
    {
      pre = _G (not (Add ((q [@d]), x, u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, v);
    };
    {
      pre =
        _U
          (not (Add ((q [@d]), x, u, true)))
          (Add ((q [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (Add ((q [@d]), b, u, true)))
                  && not (Take ((q [@d]), y, true)))
                  (Add ((q [@d]), (c2 [@d]), u, true)
                  && _X
                       (_U
                          ((not (Add ((q [@d]), b, u, true)))
                          && not (Take ((q [@d]), y, true)))
                          (Take ((q [@d]), (c1 [@d]), true)
                          && _X
                               (_U
                                  ((not (Add ((q [@d]), b, u, true)))
                                  && not (Take ((q [@d]), y, true)))
                                  (Take ((q [@d]), (c2 [@d]), true)
                                  && _X (_G (not (Add ((q [@d]), z, u, true))))
                                  )))))));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, v);
    };
    {
      pre =
        _U
          (not (Add ((q [@d]), x, u, true)))
          (Add ((q [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (Add ((q [@d]), b, u, true)))
                  && not (Take ((q [@d]), y, true)))
                  (Add ((q [@d]), (c2 [@d]), u, true)
                  && _X (_G (not (Take ((q [@d]), z, true)))))));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, not v);
    };
    {
      pre =
        _U
          (not (Add ((q [@d]), x, u, true)))
          (Add ((q [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (Add ((q [@d]), b, u, true)))
                  && not (Take ((q [@d]), y, true)))
                  (Add ((q [@d]), (c2 [@d]), u, true)
                  && _X
                       (_U
                          ((not (Add ((q [@d]), b, u, true)))
                          && not (Take ((q [@d]), y, true)))
                          (Take ((q [@d]), (c1 [@d]), true)
                          && _X (_G (not (Take ((q [@d]), z, true)))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, not v);
    };
  |]

let[@libRty] add ?l:(q = (true : [%v: Queue.t])) ?l:(c = (true : [%v: Char.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Add ((q [@d]), (c [@d]), v, true);
  }

let[@libRty] take ((co : Char.t) [@ghost]) ((c : Char.t) [@ghost])
    ?l:(q = (true : [%v: Queue.t])) =
  {
    pre =
      _U
        (not (Add ((q [@d]), x, u, true)))
        (Add ((q [@d]), (c [@d]), u, true)
         && _X (_G (not (Take ((q [@d]), y, true))))
        || Add ((q [@d]), (co [@d]), u, true)
           && _U
                ((not (Add ((q [@d]), b, u, true)))
                && not (Take ((q [@d]), y, true)))
                (Add ((q [@d]), (c [@d]), u, true)
                && _X
                     (_U
                        (not (Take ((q [@d]), y, true)))
                        (Take ((q [@d]), (co [@d]), true)))));
    res = (v == c : [%v: Char.t]);
    newadding = lastL && Take ((q [@d]), v, v == c);
  }

let[@libRty] atEOS ((c1 : Char.t) [@ghost]) ((c2 : Char.t) [@ghost])
    ?l:(s = (true : [%v: Stream.t])) =
  [|
    {
      pre = _G (not (PutChar ((s [@d]), x, u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, v);
    };
    {
      pre =
        _U
          (not (PutChar ((s [@d]), x, u, true)))
          (PutChar ((s [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (PutChar ((s [@d]), b, u, true)))
                  && not (GetChar ((s [@d]), y, true)))
                  (PutChar ((s [@d]), (c2 [@d]), u, true)
                  && _X
                       (_U
                          ((not (PutChar ((s [@d]), b, u, true)))
                          && not (GetChar ((s [@d]), y, true)))
                          (GetChar ((s [@d]), (c1 [@d]), true)
                          && _X
                               (_U
                                  ((not (PutChar ((s [@d]), b, u, true)))
                                  && not (GetChar ((s [@d]), y, true)))
                                  (GetChar ((s [@d]), (c2 [@d]), true)
                                  && _X
                                       (_G
                                          (not (PutChar ((s [@d]), z, u, true))))
                                  )))))));
      res = (v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, v);
    };
    {
      pre =
        _U
          (not (PutChar ((s [@d]), x, u, true)))
          (PutChar ((s [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (PutChar ((s [@d]), b, u, true)))
                  && not (GetChar ((s [@d]), y, true)))
                  (PutChar ((s [@d]), (c2 [@d]), u, true)
                  && _X (_G (not (GetChar ((s [@d]), z, true)))))));
      res = (not v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, not v);
    };
    {
      pre =
        _U
          (not (PutChar ((s [@d]), x, u, true)))
          (PutChar ((s [@d]), (c1 [@d]), u, true)
          && _X
               (_U
                  ((not (PutChar ((s [@d]), b, u, true)))
                  && not (GetChar ((s [@d]), y, true)))
                  (PutChar ((s [@d]), (c2 [@d]), u, true)
                  && _X
                       (_U
                          ((not (PutChar ((s [@d]), b, u, true)))
                          && not (GetChar ((s [@d]), y, true)))
                          (GetChar ((s [@d]), (c1 [@d]), true)
                          && _X (_G (not (GetChar ((s [@d]), z, true)))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, not v);
    };
  |]

let[@libRty] putChar ?l:(s = (true : [%v: Stream.t]))
    ?l:(c = (true : [%v: Char.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutChar ((s [@d]), (c [@d]), v, true);
  }

let[@libRty] getChar ((co : Char.t) [@ghost]) ((c : Char.t) [@ghost])
    ?l:(s = (true : [%v: Stream.t])) =
  {
    pre =
      _U
        (not (PutChar ((s [@d]), x, u, true)))
        (PutChar ((s [@d]), (c [@d]), u, true)
         && _X (_G (not (GetChar ((s [@d]), y, true))))
        || PutChar ((s [@d]), (co [@d]), u, true)
           && _U
                ((not (PutChar ((s [@d]), b, u, true)))
                && not (GetChar ((s [@d]), y, true)))
                (PutChar ((s [@d]), (c [@d]), u, true)
                && _X
                     (_U
                        (not (GetChar ((s [@d]), y, true)))
                        (GetChar ((s [@d]), (co [@d]), true)))));
    res = (v == c : [%v: Char.t]);
    newadding = lastL && GetChar ((s [@d]), v, v == c);
  }

