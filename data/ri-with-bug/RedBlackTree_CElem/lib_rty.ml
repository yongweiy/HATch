let[@libRty] setLeft ?l:(parent = (true : [%v: CElem.t]))
    ?l:(child = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetLeft ((parent [@d]), b, u, true));
       Append (SetLeft (parent, child, ())));
  }

let[@libRty] getLeft ?l:(parent = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: CElem.t]);
    eff =
      Admit
        (_U
           (not (SetLeft ((parent [@d]), a, u, true)))
           (SetLeft ((parent [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetLeft ((parent [@d]), a, u, true))))));
  }

let[@libRty] setRight ?l:(parent = (true : [%v: CElem.t]))
    ?l:(child = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetRight ((parent [@d]), b, u, true));
       Append (SetRight (parent, child, ())));
  }

let[@libRty] getRight ?l:(parent = (true : [%v: CElem.t])) =
  {
    ret = (true : [%v: CElem.t]);
    eff =
      Admit
        (_U
           (not (SetRight ((parent [@d]), a, u, true)))
           (SetRight ((parent [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetRight ((parent [@d]), a, u, true))))));
  }

(* let[@libRty] isExtern ?l:(parent = (true : [%v: CElem.t])) = *)
(*   { *)
(*     ret = (v : [%v: bool]); *)
(*     eff = *)
(*       Admit *)
(*         (_U *)
(*            (not (SetLeft ((parent [@d]), a, u, true))) *)
(*            (SetLeft ((parent [@d]), a, u, is_leaf a) *)
(*            && _X (_G (not (SetLeft ((parent [@d]), a, u, true))))) *)
(*         && _U *)
(*              (not (SetRight ((parent [@d]), a, u, true))) *)
(*              (SetRight ((parent [@d]), a, u, is_leaf a) *)
(*              && _X (_G (not (SetRight ((parent [@d]), a, u, true)))))); *)
(*   } *)
