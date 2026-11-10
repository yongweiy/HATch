(* Queue operations *)
let[@libRty] create ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Queue.t]);
    eff =
      (Admit (_G (not (Create (u, (ret [@d]), true))));
       Append (Create ((), ret)));
  }

let[@libRty] isEmpty ?l:(q = (true : [%v: Queue.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_F
                (Create (u, (q [@d]), true)
                && _X (_G (not (Add (a, (q [@d]), u, true))))))),
          (Guard (not ret);
           Admit
             (_F
                (Create (u, (q [@d]), true)
                && _X (_F (Add (a, (q [@d]), u, true)))))) );
  }

let[@libRty] add ?l:(a = (true : [%v: Node.t])) ?l:(q = (true : [%v: Queue.t]))
    =
  {
    ret = (true : [%v: unit]);
    eff =
      (Admit (_F (Create (u, (q [@d]), true)));
       Append (Add (a, q, ())));
  }

let[@libRty] take ?l:(q = (true : [%v: Queue.t])) =
  {
    ret = (true : [%v: Node.t]);
    eff =
      (Admit
         (_F
            (Create (u, (q [@d]), true)
            && _X
                 (_U
                    (not (Add (a, (q [@d]), u, true)))
                    (Add ((ret [@d]), (q [@d]), u, true)))));
       Reject (Add ((ret [@d]), (q [@d]), u, true)));
  }

(* Graph operations *)
let[@libRty] connect ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (Connect ((s1 [@d]), (s2 [@d]), u, true));
       Append (Connect (s1, s2, ())));
  }

let[@libRty] isConnected ?l:(s1 = (true : [%v: Node.t]))
    ?l:(s2 = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (Connect ((s1 [@d]), (s2 [@d]), u, true)))
                (Connect ((s1 [@d]), (s2 [@d]), u, true)
                && _X (not (_F (Connect ((s1 [@d]), (s2 [@d]), u, true))))))),
          (Guard (not ret);
           Admit (_G (not (Connect ((s1 [@d]), (s2 [@d]), u, true))))) );
  }

let[@libRty] getNeighbors ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: Iterator.t]);
    eff =
      (Admit (_G (not (GetNeighbors (s, (ret [@d]), true))));
       Append (GetNeighbors (s, ret)));
  }

(* Iterator operations *)
let[@libRty] hasNext ?l:(s = (true : [%v: Node.t]))
    ?l:(it = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      (let (last : Node.t) = (true : [%v: Node.t]) in
       Choice
         ( (Guard ret;
            Admit
              (_F
                 (Connect ((s [@d]), (last [@d]), u, true)
                 && _X
                      (_F
                         (GetNeighbors ((s [@d]), (it [@d]), true)
                         && _X
                              (_G
                                 (not (Next ((s [@d]), (it [@d]), (last [@d]), true))))
                         ))))),
           (Guard (not ret);
            Admit
              (_U
                 (not (Connect ((s [@d]), b, u, true)))
                 (GetNeighbors ((s [@d]), (it [@d]), true))
              || _F
                   (Connect ((s [@d]), (last [@d]), u, true)
                   && _X
                        (_U
                           (not (Connect ((s [@d]), b, u, true)))
                           (GetNeighbors ((s [@d]), (it [@d]), true)
                           && _X
                                (_F
                                   (Next ((s [@d]), (it [@d]), (last [@d]), true)
                                   && _X
                                        (_G
                                           (not (Next ((s [@d]), (it [@d]), b, true))))
                                   ))))))) ));
  }

let[@libRty] next ?l:(s = (true : [%v: Node.t]))
    ?l:(it = (true : [%v: Iterator.t])) =
  {
    ret = (true : [%v: Node.t]);
    eff =
      (let (last : Node.t) = (true : [%v: Node.t]) in
       Admit
         (_U
            (not (Connect ((s [@d]), b, u, true)))
            (Connect ((s [@d]), (ret [@d]), u, true)
            && _X
                 (_F
                    (GetNeighbors ((s [@d]), (it [@d]), true)
                    && _X (_G (not (Next ((s [@d]), (it [@d]), b, true)))))))
         || _F
              (Connect ((s [@d]), (last [@d]), u, true)
              && _X
                   (_U
                      (not (Connect ((s [@d]), b, u, true)))
                      (Connect ((s [@d]), (ret [@d]), u, true)
                      && _X
                           (_F
                              (GetNeighbors ((s [@d]), (it [@d]), true)
                              && _X
                                   (_F
                                      (Next ((s [@d]), (it [@d]), (last [@d]), true)
                                      && _X
                                           (_G
                                              (not
                                                 (Next ((s [@d]), (it [@d]), b, true))))
                                      )))))))));
  }

(* Visited tracking *)
let[@libRty] initVisited ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff = Admit (_G (not (MarkVisited (k, u, true))));
  }

let[@libRty] markVisited ?l:(k = (true : [%v: Node.t])) =
  { ret = (true : [%v: unit]); eff = Append (MarkVisited (k, ())) }

let[@libRty] isVisited ?l:(k = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (MarkVisited ((k [@d]), u, true)))
                (MarkVisited ((k [@d]), u, true)
                && _X (not (_F (MarkVisited ((k [@d]), u, true))))))),
          (Guard (not ret);
           Admit (_G (not (MarkVisited ((k [@d]), u, true))))) );
  }
