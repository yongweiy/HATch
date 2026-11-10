let[@libRty] setHead ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetHead (a, u, true));
       Append (SetHead (a, ())));
  }

let[@libRty] hasHead ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (SetHead (a, u, true)))
                (SetHead (a, u, true)
                && _X (not (_F (SetHead (a, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (SetHead (a, u, true))))) );
  }

let[@libRty] getHead ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (SetHead (a, u, true)))
           (SetHead ((ret [@d]), u, true)
           && _X (not (_F (SetHead (b, v, true))))));
  }

let[@libRty] setNext ?l:(prev = (true : [%v: Elem.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetNext ((prev [@d]), b, u, true));
       Append (SetNext (prev, a, ())));
  }

let[@libRty] delNext ?l:(a = (true : [%v: Elem.t])) =
  { ret = (true : [%v: unit]); eff = Reject (SetNext ((a [@d]), b, u, true)) }

let[@libRty] getNext ?l:(prev = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (SetNext ((prev [@d]), a, u, true)))
           (SetNext ((prev [@d]), (ret [@d]), u, true)
           && _X (not (_F (SetNext ((prev [@d]), b, v, true))))));
  }

let[@libRty] hasNext ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (SetNext ((a [@d]), b, u, true)))
                (SetNext ((a [@d]), b, u, true)
                && _X (not (_F (SetNext ((a [@d]), b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (SetNext ((a [@d]), b, u, true))))) );
  }

let[@libRty] hasPrev ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (SetNext (b, (a [@d]), u, true)))
                (SetNext (b, (a [@d]), u, true)
                && _X (not (_F (SetNext (b, (a [@d]), v, true))))))),
          (Guard (not ret);
           Admit (_G (not (SetNext (b, (a [@d]), u, true))))) );
  }
