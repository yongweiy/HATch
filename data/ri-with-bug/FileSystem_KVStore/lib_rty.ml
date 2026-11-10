let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: Bytes.t]))
    =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Put ((k [@d]), b, u, true));
       Append (Put (k, a, ())));
  }

let[@libRty] exists ?l:(k = (true : [%v: Path.t])) =
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

let[@libRty] get ?l:(k = (true : [%v: Path.t])) =
  {
    ret = (true : [%v: Bytes.t]);
    eff =
      Admit
        (_U
           (not (Put ((k [@d]), a, u, true)))
           (Put ((k [@d]), (ret [@d]), u, true)
           && _X (not (_F (Put ((k [@d]), a, u, true)))))
        && _G
             (AddChild ((ret [@d]), child, u, k == parent child)
             || not (AddChild ((ret [@d]), child, u, true))));
  }

let[@libRty] del ?l:(k = (true : [%v: Path.t])) =
  { ret = (true : [%v: unit]); eff = Reject (Put ((k [@d]), a, u, true)) }

let[@libRty] isDir ?l:(bytes = (true : [%v: Bytes.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (AddChild ((bytes [@d]), child, u, true)))),
          (Guard (not ret);
           Admit (_G (not (AddChild ((bytes [@d]), child, u, true))))) );
  }

let[@libRty] memChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (AddChild ((bytes [@d]), (child [@d]), u, true)))),
          (Guard (not ret);
           Admit (_G (not (AddChild ((bytes [@d]), (child [@d]), u, true))))) );
  }

let[@libRty] addChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (AddChild ((bytes [@d]), (child [@d]), u, true));
       Append (AddChild (bytes, child, ())));
  }

let[@libRty] delChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Reject (AddChild ((bytes [@d]), (child [@d]), u, true));
  }

let[@libRty] getChildren ?l:(bytes = (true : [%v: Bytes.t])) =
  {
    ret = (true : [%v: Iterator.t]);
    eff =
      (Admit (not (_F (GetChildren ((bytes [@d]), it, true))));
       Append (GetChildren (bytes, ret)));
  }

let[@libRty] hasNext ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(iter = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      let (child : Path.t) = (true : [%v: Path.t])in
      Choice
        ( (Guard ret;
           Admit
              (_F
                (AddChild ((bytes [@d]), (child [@d]), u, true)
                && _X
                     (_F
                        (GetChildren ((bytes [@d]), (iter [@d]), true)
                        && _X
                             (not
                                (_F
                                   (Next
                                      ( (bytes [@d]),
                                        (iter [@d]),
                                        (child [@d]),
                                        true ))))))))
           (* (_F *)
           (*    (AddChild ((bytes [@d]), child, u, true) *)
           (*    && _X (_F (GetChildren ((bytes [@d]), (iter [@d]), true))))) *)),
          (Guard (not ret);
           Admit
             (_U
                (not (AddChild ((bytes [@d]), child, u, true)))
                (GetChildren ((bytes [@d]), (iter [@d]), true)))) );
  }

let[@libRty] next ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(iter = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: Path.t]);
    eff =
      (Admit
         (_F
            (AddChild ((bytes [@d]), (ret [@d]), u, true)
            && _X
                 (_F
                    (GetChildren ((bytes [@d]), (iter [@d]), true)
                    && _X
                         (not
                            (_F
                               (Next
                                  ((bytes [@d]), (iter [@d]), (ret [@d]), true))))
                    ))));
       Append (Next (bytes, iter, ret)));
  }
