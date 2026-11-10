let[@assertRty] next ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elt.t]);
    eff = ()(* reject last  *);
  }
