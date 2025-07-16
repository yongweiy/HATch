let[@libRty] read ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (Write (v, u, true)))
           (Write ((ret [@d]), u, true) && _X (not (_F (Write (v, u, true))))));
  }

let[@libRty] write ?l:(s = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Write (v, u, true));
       Append (Write (s, ())));
  }
