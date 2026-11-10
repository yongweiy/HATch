let[@libRty] putRoot ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutRoot ((a [@d]), u, true));
       Append (PutRoot (a, ())));
  }

let[@libRty] addLeft ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (AddLeft ((a [@d]), c, u, true));
       Append (AddLeft (a, b, ())));
  }

let[@libRty] addRight ?l:(a = (true : [%v: Elem.t]))
    ?l:(b = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (AddRight ((a [@d]), c, u, true));
       Append (AddRight (a, b, ())));
  }

let[@libRty] hasRoot ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutRoot (a, u, true)))
                (PutRoot (a, u, true) && _X (not (_F (PutRoot (b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutRoot (a, u, true))))) );
  }

let[@libRty] hasLeft ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (AddLeft ((a [@d]), b, u, true)))
                (AddLeft ((a [@d]), b, u, true)
                && _X (not (_F (AddLeft ((a [@d]), c, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (AddLeft ((a [@d]), b, u, true))))) );
  }

let[@libRty] hasRight ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (AddRight ((a [@d]), b, u, true)))
                (AddRight ((a [@d]), b, u, true)
                && _X (not (_F (AddRight ((a [@d]), c, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (AddRight ((a [@d]), b, u, true))))) );
  }

let[@libRty] getRoot ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutRoot (a, u, true)))
           (PutRoot ((ret [@d]), u, true)
           && _X (not (_F (PutRoot (a, u, true))))));
  }

let[@libRty] getLeft ?l:(b = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (AddLeft ((b [@d]), a, u, true)))
           (AddLeft ((b [@d]), (ret [@d]), u, true)
           && _X (not (_F (AddLeft ((b [@d]), c, v, true))))));
  }

let[@libRty] getRight ?l:(b = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (AddRight ((b [@d]), a, u, true)))
           (AddRight ((b [@d]), (ret [@d]), u, true)
           && _X (not (_F (AddRight ((b [@d]), c, v, true))))));
  }
