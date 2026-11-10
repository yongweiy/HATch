let[@libRty] newNode ?l:(a = (true : [%v: unit])) =
  { ret = (true : [%v: Node.t]); eff = Append (NewNode ((), ret)) }

let[@libRty] putNodeContent ?l:(s = (true : [%v: Node.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutNodeContent ((s [@d]), b, u, true));
       Append (PutNodeContent (s, a, ())));
  }

let[@libRty] hasNodeContent ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutNodeContent ((s [@d]), a, u, true)))
                (PutNodeContent ((s [@d]), a, u, true)
                && _X (not (_F (PutNodeContent ((s [@d]), a, u, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutNodeContent ((s [@d]), a, u, true))))) );
  }

let[@libRty] getNodeContent ?l:(c = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutNodeContent ((c [@d]), a, u, true)))
           (PutNodeContent ((c [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutNodeContent ((c [@d]), a, u, true))))));
  }

let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Connect ((s1 [@d]), (s2 [@d]), u, true));
       Append (Connect (s1, s2, ())));
  }

let[@libRty] isConnected ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Connect ((s1 [@d]), (s2 [@d]), u, true)))
                (Connect ((s1 [@d]), (s2 [@d]), u, true)
                && _X (not (_F (Connect ((s1 [@d]), (s2 [@d]), u, true))))))),
          (Guard (not ret);
           Admit (_G (not (Connect ((s1 [@d]), (s2 [@d]), u, true))))) );
  }

let[@libRty] hasConnectIn ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (Connect (a, (s [@d]), u, true)))),
          (Guard (not ret);
           Admit (_G (not (Connect (a, (s [@d]), u, true))))) );
  }

let[@libRty] hasConnectOut ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (Connect ((s [@d]), a, u, true)))),
          (Guard (not ret);
           Admit (_G (not (Connect ((s [@d]), a, u, true))))) );
  }
