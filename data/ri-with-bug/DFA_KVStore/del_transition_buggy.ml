let del_transition (st : Node.t) (ch : Char.t) (en : Node.t) : unit =
  if exists st ch then (
    del st ch;
    put en ch st;
    ())
  else ()

(* Incorrectness specification: the del_transition function deletes a transition
   but then creates an invalid replacement mapping *)

let[@assertRty] del_transition ?l:(st = (true : [%v: Node.t])) 
    ?l:(ch = (true : [%v: Char.t])) ?l:(en = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (Exists (st, ch, true);
           Exists (en, ch, true)) );
  }
