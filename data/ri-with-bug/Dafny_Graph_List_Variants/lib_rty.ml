(* Queue operations *)
let[@libRty] isEmpty ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_G (not (Add (a, u, true))))),
          (Guard (not ret);
           Admit (_F (Add (a, u, true)))) );
  }

let[@libRty] add ?l:(a = (true : [%v: Node.t])) =
  { ret = (true : [%v: unit]); eff = Append (Add (a, ())) }

let[@libRty] take ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Node.t]);
    eff =
      (Admit (_U (not (Add (a, u, true))) (Add ((ret [@d]), u, true)));
       Reject (Add ((ret [@d]), u, true)));
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

let[@libRty] getNeighbors ?l:(s = (true : [%v: Node.t])) =
  {
    ret = (is_nil (tl (tl v)) : [%v: NodeList.t]);
    eff =
      Admit
        (_U
           (not (Connect ((s [@d]), a, u, true)))
           (Connect ((s [@d]), a, u, a == hd ret)
           && _X
                (_U
                   (not (Connect ((s [@d]), a, u, true)))
                   (Connect ((s [@d]), a, u, a == hd (tl ret))
                   && _X (_G (not (Connect ((s [@d]), a, u, true))))))));
  }

(* let[@libRty] getNeighbors ?l:(s = (true : [%v: Node.t])) = *)
(*   { *)
(*     ret = (is_nil (tl v) : [%v: NodeList.t]); *)
(*     eff = *)
(*       Admit *)
(*         (_U *)
(*            (not (Connect ((s [@d]), a, u, true))) *)
(*            (Connect ((s [@d]), a, u, a == hd ret) *)
(*            && _X (_G (not (Connect ((s [@d]), a, u, true)))))); *)
(*   } *)

(* Visited tracking *)
let[@libRty] initVisited ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff = Admit (_G (not (MarkVisited (k, u, true))));
  }

let[@libRty] markVisited ?l:(k = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (
        (* Admit (_G (not (MarkVisited ((k [@d]), u, true)))); *)
       Append (MarkVisited (k, ())));
  }

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
                && _X (_G (not (MarkVisited ((k [@d]), u, true))))))),
          (Guard (not ret);
           Admit (_G (not (MarkVisited ((k [@d]), u, true))))) );
  }
