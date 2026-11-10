let rec append (hd : Node.t) (x : Elem.t) : unit =
  if hasNodeContent hd then
    if hasConnectOut hd then ()
    else
      let (c : Node.t) = newNode () in
      if hasConnectIn c then (
        append hd x;
        ())
      (* else if node_eq hd c then ( *)
        (* append hd x; *)
        (* ()) *)
      else (
        connect hd c;
        putNodeContent c x;
        ())
  else (
    putNodeContent hd x;
    ())

(* Incorrectness specification: the append function can create self-referential connections
   by connecting a node to itself, violating the representation invariant *)

let[@assertRty] append ?l:(hd = (true : [%v: Node.t]))
    ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Constrain ((), Connect (hd, hd, ()));
  }
