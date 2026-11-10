let[@libRty] putC ?l:(k = (true : [%v: Cell.t]))
    ?l:(next = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutC ((k [@d]), b, u, true));
       Append (PutC (k, next, ())));
  }

let[@libRty] putE ?l:(k = (true : [%v: Cell.t])) ?l:(a = (true : [%v: Elem.t]))
    =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutE ((k [@d]), b, u, true));
       Append (PutE (k, a, ())));
  }

let[@libRty] getC ?l:(k = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Cell.t]);
    eff =
      Admit
        (_U
           (not (PutC ((k [@d]), a, u, true)))
           (PutC ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutC ((k [@d]), a, u, true))))));
  }

let[@libRty] getE ?l:(k = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutE ((k [@d]), a, u, true)))
           (PutE ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutE ((k [@d]), a, u, true))))));
  }

let[@libRty] existsC ?l:(k = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutC ((k [@d]), a, u, true)))
                (PutC ((k [@d]), a, u, true)
                && _X (not (_F (PutC ((k [@d]), b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutC ((k [@d]), a, u, true))))) );
  }

let[@libRty] existsValC ?l:(k = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (PutE ((k [@d]), a, u, true)))),
          (Guard (not ret);
           Admit (_G (not (PutE ((k [@d]), a, u, true))))) );
  }

let[@libRty] existsE ?l:(k = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutE ((k [@d]), a, u, true)))
                (PutE ((k [@d]), a, u, true)
                && _X (not (_F (PutE ((k [@d]), b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutE ((k [@d]), a, u, true))))) );
  }

let[@libRty] newCell ?l:(k = (true : [%v: unit])) =
  {
    ret = (true : [%v: Cell.t]);
    eff = Append (NewCell ((), ret));
  }
