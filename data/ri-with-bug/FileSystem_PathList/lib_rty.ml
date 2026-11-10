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

let[@libRty] getParent ?l:(a = (true : [%v: Path.t])) =
  {
    ret = (v == parent a : [%v: Path.t]);
    eff = Admit (Any true);
  }

let[@libRty] isRoot ?l:(a = (true : [%v: Path.t])) =
  {
    ret = (v == is_root a : [%v: bool]);
    eff = Admit (Any true);
  }

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
    ret = (true : [%v: PathList.t]);
    eff = Admit (Any true);
  }
