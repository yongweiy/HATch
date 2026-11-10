let[@libRty] create ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Set.t]);
    eff = Admit (_G (not (Add (a, (ret [@d]), u, true))));
  }

let[@libRty] add ?l:(a = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Add ((a [@d]), (s [@d]), u, true));
       Append (Add (a, s, ())));
  }

let[@libRty] mem ?l:(a = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Add ((a [@d]), (s [@d]), u, true)))
                (Add ((a [@d]), (s [@d]), u, true)
                && _X (_G (not (Add ((a [@d]), (s [@d]), u, true))))))),
          (Guard (not ret);
           Admit (_G (not (Add ((a [@d]), (s [@d]), u, true))))) );
  }

let[@libRty] isEmpty ?l:(s = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_G (not (Add (a, (s [@d]), u, true))))),
          (Guard (not ret);
           Admit (_F (Add (a, (s [@d]), u, true)))) );
  }

let[@libRty] getIter ?l:(s = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: Iter.t]);
    eff =
      (Admit (_G (not (GetIter (r, (ret [@d]), true))));
       Append (GetIter (s, ret)));
  }

let[@libRty] hasIter ?l:(it = (true : [%v: Iter.t]))
    ?l:(s = (true : [%v: Set.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (GetIter (s, (it [@d]), true)))
                (GetIter ((s [@d]), (it [@d]), true)
                && _X (_G (not (GetIter (s, (it [@d]), true))))))),
          (Guard (not ret);
           Admit (_G (not (GetIter ((s [@d]), (it [@d]), true))))) );
  }

let[@libRty] next ?l:(it = (true : [%v: Iter.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      (let (s : Set.t) = (true : [%v: Set.t]) in
       let (last : Elem.t) = (true : [%v: Elem.t]) in
       Admit
         (_F
            (Add ((last [@d]), (s [@d]), u, true)
            && _X
                 (_U
                    (not (Add (b, (s [@d]), u, true)))
                    (Add ((ret [@d]), (s [@d]), u, true)
                    && _X
                         (_F
                            (GetIter ((s [@d]), (it [@d]), true)
                            && _X
                                 (_F
                                    (Next ((it [@d]), (last [@d]), true)
                                    && _X (_G (not (Next ((it [@d]), b, true))))
                                    ))))))));
       Append (Next (it, ret)));
  }

let[@libRty] hasNext ?l:(it = (true : [%v: Iter.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      (let (last : Elem.t) = (true : [%v: Elem.t]) in
       let (s : Set.t) = (true : [%v: Set.t]) in
       Choice
         ( (Guard ret;
            Admit
              (_F
                 (Add ((last [@d]), (s [@d]), u, true)
                 && _X
                      (_F
                         (GetIter ((s [@d]), (it [@d]), true)
                         && _X (_G (not (Next ((it [@d]), (last [@d]), true))))
                         ))))),
           (Guard (not ret);
            Admit
              (_F
                 (Add ((last [@d]), (s [@d]), u, true)
                 && _X
                      (_U
                         (not (Add (b, (s [@d]), u, true)))
                         (GetIter ((s [@d]), (it [@d]), true)
                         && _X
                              (_F
                                 (Next ((it [@d]), (last [@d]), true)
                                 && _X (_G (not (Next ((it [@d]), b, true))))))
                         ))))) ));
  }
