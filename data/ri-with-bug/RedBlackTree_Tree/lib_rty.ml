(* Pointer operations *)
let[@libRty] createPtr ?l:(u = (true : [%v: unit])) =
  { ret = (true : [%v: Ptr.t]); eff = Append (CreatePtr ((), ret)) }

(* Value KV store operations *)
let[@libRty] getValue ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (SetValue ((node [@d]), a, u, true)))
           (SetValue ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetValue ((node [@d]), a, u, true))))));
  }

let[@libRty] setValue ?l:(node = (true : [%v: Ptr.t]))
    ?l:(value = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetValue ((node [@d]), b, u, true));
       Append (SetValue (node, value, ())));
  }

(* Tree structure queries *)
let[@libRty] isLeaf ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_G (not (SetLeft ((node [@d]), a, u, true)))
             && _G (not (SetRight ((node [@d]), a, u, true))))),
          (Guard (not ret);
           Admit
             (_F (SetLeft ((node [@d]), a, u, true))
             || _F (SetRight ((node [@d]), a, u, true)))) );
  }

let[@libRty] getColor ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Admit
        (_U
           (not (SetColor ((node [@d]), a, u, true)))
           (SetColor ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetColor ((node [@d]), a, u, true))))));
  }

let[@libRty] setColor ?l:(node = (true : [%v: Ptr.t]))
    ?l:(color = (true : [%v: bool])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetColor ((node [@d]), b, u, true));
       Append (SetColor (node, color, ())));
  }

(* Node property access *)
let[@libRty] getLeft ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (not (v == node) : [%v: Ptr.t]);
    eff =
      Admit
        (_U
           (not (SetLeft ((node [@d]), a, u, true)))
           (SetLeft ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetLeft ((node [@d]), a, u, true))))));
  }

let[@libRty] getRight ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (not (v == node) : [%v: Ptr.t]);
    eff =
      Admit
        (_U
           (not (SetRight ((node [@d]), a, u, true)))
           (SetRight ((node [@d]), (ret [@d]), u, true)
           && _X (_G (not (SetRight ((node [@d]), a, u, true))))));
  }

(* Node structure mutation *)
let[@libRty] setLeft ?l:(node = (true : [%v: Ptr.t]))
    ?l:(child = (not (v == node) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetLeft ((node [@d]), b, u, true));
       Append (SetLeft (node, child, ())));
  }

let[@libRty] setRight ?l:(node = (true : [%v: Ptr.t]))
    ?l:(child = (not (v == node) : [%v: Ptr.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetRight ((node [@d]), b, u, true));
       Append (SetRight (node, child, ())));
  }

let[@libRty] hasLeft ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (SetLeft ((node [@d]), a, u, true)))),
          (Guard (not ret);
           Admit (_G (not (SetLeft ((node [@d]), a, u, true))))) );
  }

let[@libRty] hasRight ?l:(node = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (SetRight ((node [@d]), a, u, true)))),
          (Guard (not ret);
           Admit (_G (not (SetRight ((node [@d]), a, u, true))))) );
  }
