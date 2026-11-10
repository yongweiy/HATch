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
