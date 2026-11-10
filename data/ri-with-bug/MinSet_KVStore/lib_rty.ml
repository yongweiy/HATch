let[@libRty] put ?l:(k = (true : [%v: Key.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Put ((k [@d]), b, u, true));
       Append (Put (k, a, ())));
  }

let[@libRty] get ?l:(k = (true : [%v: Key.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (Put ((k [@d]), a, u, true)))
           (Put ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (Put ((k [@d]), a, u, true))))));
  }

let[@libRty] exists ?l:(k = (true : [%v: Key.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Put ((k [@d]), a, u, true)))
                (Put ((k [@d]), ret, u, true)
                && _X (not (_F (Put ((k [@d]), a, u, true))))))),
          (Guard (not ret);
           Admit (_G (not (Put ((k [@d]), v, u, true))))) );
  }

let[@libRty] hasValue ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Put (v, (a [@d]), u, true)))
                (Put (u, (a [@d]), ret, true)
                && _X (not (_F (Put (w, (a [@d]), x, true))))))),
          (Guard (not ret);
           Admit (_G (not (Put (v, (a [@d]), u, true))))) );
  }

let[@libRty] randomKey ?l:(k = (true : [%v: unit])) =
  { ret = (true : [%v: Key.t]); eff = () }

let[@libRty] write ?l:(idx = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Write ((idx [@d]), u, true));
       Append (Write (idx, ())));
  }

let[@libRty] isWritten ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Write (a, u, true)))
                (Write (a, u, true) && _X (not (_F (Write (b, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (Write (a, u, true))))) );
  }

let[@libRty] read ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (Write ((ret [@d]), u, true)))
           (Write ((ret [@d]), u, true) && _X (not (_F (Write (a, v, true))))));
  }
