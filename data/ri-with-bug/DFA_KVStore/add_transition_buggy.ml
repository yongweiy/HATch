let add_transition (st : Node.t) (ch : Char.t) (en : Node.t) : unit =
  if exists st ch then ()
  else (
    put en ch st;
    ())

(* Incorrectness specification: the add_transition function can create invalid
   state transitions by putting the mapping in wrong order *)

let[@assertRty] add_transition ?l:(st = (true : [%v: Node.t])) 
    ?l:(ch = (true : [%v: Char.t])) ?l:(en = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (Exists (st, ch, false);
           Exists (en, ch, true)) );
  }
