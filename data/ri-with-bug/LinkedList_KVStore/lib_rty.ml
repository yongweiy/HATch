let[@libRty] putNext ?l:(k = (true : [%v: Ptr.t])) ?l:(a = (true : [%v: Ptr.t]))
    =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutNext ((k [@d]), b, u, true));
       Append (PutNext (k, a, ())));
  }

let[@libRty] getNext ?l:(k = (not (is_nullptr v) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      Admit
        (_U
           (not (PutNext ((k [@d]), a, u, true)))
           (PutNext ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutNext ((k [@d]), a, u, true))))));
  }

let[@libRty] delNext ?l:(k = (not (is_nullptr v) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      (Admit
         (_U
            (not (PutNext ((k [@d]), a, u, true)))
            (PutNext ((k [@d]), (ret [@d]), u, true)
            && _X (not (_F (PutNext ((k [@d]), a, u, true))))));
       Reject (PutNext ((k [@d]), v, u, true)));
  }

let[@libRty] hasPrev ?l:(k = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (PutNext (b, (k [@d]), u, true)))),
          (Guard (not ret);
           Admit (_G (not (PutNext (b, (k [@d]), u, true))))) );
  }

let[@libRty] putVal ?l:(k = (true : [%v: Ptr.t])) ?l:(a = (true : [%v: Elem.t]))
    =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutVal ((k [@d]), b, u, true));
       Append (PutVal (k, a, ())));
  }

let[@libRty] getVal ?l:(k = (not (is_nullptr v) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutVal ((k [@d]), a, u, true)))
           (PutVal ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutVal ((k [@d]), a, u, true))))));
  }
