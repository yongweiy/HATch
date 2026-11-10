let[@libRty] addNode ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (AddNode ((s [@d]), u, true));
       Append (AddNode (s, ())));
  }

let[@libRty] isNode ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( Seq
            ( Guard ret,
              Admit
                (_U
                   (not (AddNode ((s [@d]), u, true)))
                   (AddNode ((s [@d]), u, true)
                   && _X (not (_F (AddNode ((s [@d]), u, true)))))) ),
          Seq (Guard (not ret), Admit (_G (not (AddNode ((s [@d]), u, true)))))
        );
  }

let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  { ret = (true : [%v: unit]); eff = Append (Connect (s1, c, s2, ())) }

let[@libRty] disconnect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Reject (Connect ((s1 [@d]), (c [@d]), (s2 [@d]), (), true));
  }

let[@libRty] isConnected ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        (Seq
           ( Guard ret,
             Admit (Connect ((s1 [@d]), (c [@d]), (s2 [@d]), (), true)) );
         Guard
           ( not (is_trans s1 c s2),
             Append (IsConnected ((s1 [@d]), (c [@d]), (s2 [@d]), (), false)) ));
  }

let[@libRty] hasOutEdge ?l:(s1 = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        (Guard
           ( has_out_edge s1 c,
             Append (HasOutEdge ((s1 [@d]), (c [@d]), (), true)) );
         Guard
           ( not (has_out_edge s1 c),
             Append (HasOutEdge ((s1 [@d]), (c [@d]), (), false)) ));
  }
