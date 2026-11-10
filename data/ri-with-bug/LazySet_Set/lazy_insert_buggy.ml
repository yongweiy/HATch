let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  thunk ();
  if not (mem x) then ()
  else (
    insert x;
    ())

(* Incorrectness specification: the lazy_insert function has inverted logic
   and inserts elements that are already members instead of non-members *)

let[@assertRty] lazy_insert ?l:(x = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      Constrain
        ( (),
          (Mem (x, true);
           Mem (x, true)) );
  }
