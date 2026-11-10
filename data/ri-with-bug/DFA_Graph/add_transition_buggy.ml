let add_transition (st : Node.t) (ch : Char.t) (en : Node.t) : unit =
  if isNode st then
    if isNode en then
      if not (hasOutEdge st ch) then ()
      else (
        connect st ch en;
        ())
    else ()
  else ()

(* Incorrectness specification: the add_transition function has the logic inverted -
   it connects when hasOutEdge returns true (should not add edge if it exists) *)

let[@assertRty] add_transition ?l:(st = (true : [%v: Node.t])) 
    ?l:(ch = (true : [%v: Char.t])) ?l:(en = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (IsNode (st, true);
           IsNode (en, true);
           HasOutEdge (st, ch, true);
           IsConnected (st, ch, en, true)) );
  }
