(* DOM node operations *)
let[@libRty] getClassName ?l:(node = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (SetClassName ((node [@d]), a, u, true)))
           (SetClassName ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetClassName ((node [@d]), a, u, true))))));
  }

let[@libRty] getNodeId ?l:(node = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (SetNodeId ((node [@d]), a, u, true)))
           (SetNodeId ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetNodeId ((node [@d]), a, u, true))))));
  }

let[@libRty] setNodeId ?l:(node = (true : [%v: Node.t]))
    ?l:(nodeId = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetNodeId ((node [@d]), b, u, true));
       Append (SetNodeId (node, nodeId, ())));
  }

let[@libRty] setClassName ?l:(node = (true : [%v: Node.t]))
    ?l:(className = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetClassName ((node [@d]), b, u, true));
       Append (SetClassName (node, className, ())));
  }

let[@libRty] getChildren ?l:(node = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: Iterator.t]);
    eff =
      (Admit (_G (not (GetChildren ((node [@d]), it, true))));
       Append (GetChildren (node, ret)));
  }

let[@libRty] addChild ?l:(parent = (true : [%v: Node.t]))
    ?l:(child = (true : [%v: Node.t])) =
  { ret = (true : [%v: unit]); eff = Append (AddChild (parent, child, ())) }

(* DOM tree traversal *)
let[@libRty] findByClass ?l:(parent = (true : [%v: Node.t]))
    ?l:(className = (true : [%v: int])) =
  {
    ret = (not (v == parent) : [%v: Node.t]);
    eff =
      Admit
        (_U
           (not (SetClassName ((ret [@d]), a, u, true)))
           (SetClassName ((ret [@d]), (className [@d]), u, true)
           && _X
                (_G (not (SetClassName ((ret [@d]), a, u, true)))
                && _F (AddChild ((parent [@d]), (ret [@d]), u, true)))));
  }

(* Iterator operations that track visited children via Next events *)
let[@libRty] hasNext ?l:(iter = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      (let (parent : Node.t) = (true : [%v: Node.t]) in
       let (child : Node.t) = (true : [%v: Node.t]) in
       Choice
         ( (Guard ret;
            Admit
              (_F
                 (AddChild ((parent [@d]), (child [@d]), u, true)
                 && _X
                      (_F
                         (GetChildren ((parent [@d]), (iter [@d]), true)
                         && _X
                              (not
                                 (_F (Next ((iter [@d]), (child [@d]), true))))
                         ))))),
           (Guard (not ret);
            Admit
              (_U
                 (not (AddChild ((parent [@d]), child, u, true)))
                 (GetChildren ((parent [@d]), (iter [@d]), true)))) ));
  }

let[@libRty] next ?l:(iter = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: Node.t]);
    eff =
      (let (parent : Node.t) = (true : [%v: Node.t]) in
       Admit
         (_F
            (AddChild ((parent [@d]), (ret [@d]), u, true)
            && _X
                 (_F
                    (GetChildren ((parent [@d]), (iter [@d]), true)
                    && _X (not (_F (Next ((iter [@d]), (ret [@d]), true))))))));
       Append (Next (iter, ret)));
  }

(* Contact store operations *)
let[@libRty] putContact ?l:(nameId = (true : [%v: int]))
    ?l:(phoneId = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutContact ((nameId [@d]), b, u, true));
       Append (PutContact (nameId, phoneId, ())));
  }

let[@libRty] getContact ?l:(nameId = (true : [%v: int])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (PutContact ((nameId [@d]), a, u, true)))
           (PutContact ((nameId [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutContact ((nameId [@d]), a, u, true))))));
  }

let[@libRty] memContact ?l:(k = (true : [%v: int])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutContact ((k [@d]), a, u, true)))
                (PutContact ((k [@d]), a, u, true)
                && _X (not (_F (PutContact ((k [@d]), a, u, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutContact ((k [@d]), v, u, true))))) );
  }
