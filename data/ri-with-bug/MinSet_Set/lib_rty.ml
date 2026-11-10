let[@libRty] insert ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Insert ((a [@d]), u, true));
       Append (Insert (a, ())));
  }

let[@libRty] mem ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Insert ((a [@d]), u, true)))
                (Insert ((a [@d]), u, true)
                && _X (not (_F (Insert ((a [@d]), v, true))))))),
          (Guard (not ret);
           Admit (_G (not (Insert ((a [@d]), u, true))))) );
  }

let[@libRty] isEmpty ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard (not ret);
           Admit (_F (Insert (a, u, true)))),
          (Guard ret;
           Admit (_G (not (Insert (a, u, true))))) );
  }

let[@libRty] write ?l:(idx = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Write ((idx [@d]), u, true));
       Append (Write (idx, ())));
  }

let[@libRty] read ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (Write (a, u, true)))
           (Write ((ret [@d]), u, true) && _X (not (_F (Write (a, v, true))))));
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
