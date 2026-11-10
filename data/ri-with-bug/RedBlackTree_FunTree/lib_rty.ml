let[@libRty] setColor ?l:(n = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: bool])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetColor ((n [@d]), b, u, true));
       Append (SetColor (n, c, ())));
  }

let[@libRty] getColor ?l:(n = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Admit
        (_U
           (not (SetColor ((n [@d]), a, u, true)))
           (SetColor ((n [@d]), (ret [@d]), u, true)
           && _X (not (_F (SetColor ((n [@d]), a, u, true))))));
  }

let[@libRty] setValue ?l:(n = (true : [%v: Node.t]))
    ?l:(value = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetValue ((n [@d]), b, u, true));
       Append (SetValue (n, value, ())));
  }

let[@libRty] getValue ?l:(n = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (SetValue ((n [@d]), a, u, true)))
           (SetValue ((n [@d]), (ret [@d]), u, true)
           && _X (not (_F (SetValue ((n [@d]), a, u, true))))));
  }
