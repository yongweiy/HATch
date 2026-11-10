let[@libRty] read ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (Write (v, u, true)))
           (Write ((ret [@d]), u, true) && _X (not (_F (Write (v, u, true))))));
  }

let[@libRty] write ?l:(s = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Write (v, u, true));
       Append (Write (s, ())));
  }
