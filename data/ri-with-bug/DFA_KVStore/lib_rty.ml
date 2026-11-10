let[@libRty] put ?l:(a = (true : [%v: Node.t])) ?l:(c = (true : [%v: Char.t]))
    ?l:(b = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Put ((a [@d]), (c [@d]), d, u, true));
       Append (Put (a, c, b, ())));
  }

let[@libRty] get ?l:(a = (true : [%v: Node.t])) ?l:(c = (true : [%v: Char.t])) =
  {
    ret = (true : [%v: Node.t]);
    eff =
      Admit
        (_U
           (not (Put ((a [@d]), (c [@d]), b, u, true)))
           (Put ((a [@d]), (c [@d]), (ret [@d]), u, true)
           && _X (not (_F (Put ((a [@d]), (c [@d]), b, v, true))))));
  }

let[@libRty] exists ?l:(a = (true : [%v: Node.t]))
    ?l:(c = (true : [%v: Char.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Put ((a [@d]), (c [@d]), b, u, true)))
                (Put ((a [@d]), (c [@d]), (ret [@d]), u, true)
                && _X (not (_F (Put ((a [@d]), (c [@d]), b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (Put ((a [@d]), (c [@d]), b, u, true))))) );
  }

let[@libRty] del ?l:(a = (true : [%v: Node.t])) ?l:(c = (true : [%v: Char.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Put ((a [@d]), (c [@d]), b, u, false));
       Append (Del (a, c, ())));
  }
