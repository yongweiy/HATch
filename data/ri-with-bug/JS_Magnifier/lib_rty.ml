(* Event handling *)
let[@libRty] hasNextEvent ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (AddEvent (eventType, target, u, true)))),
          (Guard (not ret);
           Admit (_G (not (AddEvent (eventType, target, u, true))))) );
  }

let[@libRty] getEventTarget ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (AddEvent (typ, target, u, true)))
           (AddEvent (typ, (ret [@d]), u, true)));
  }

let[@libRty] getEventType ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (AddEvent (typ, target, u, true)))
           (AddEvent ((ret [@d]), target, u, true)));
  }

let[@libRty] nextEvent ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff = Reject (AddEvent (eventType, target, u, true));
  }

let[@libRty] addEvent ?l:(eventType = (true : [%v: int]))
    ?l:(target = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Append (AddEvent (eventType, target, ()));
  }

(* Element state tracking *)
let[@libRty] hasOldElem ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_F (PutOldElem (a, u, true)))),
          (Guard (not ret);
           Admit (_G (not (PutOldElem (a, u, true))))) );
  }

let[@libRty] getOldElem ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutOldElem (a, u, true)))
           (PutOldElem ((ret [@d]), u, true)
           && _X (not (_F (PutOldElem (a, u, true))))));
  }

let[@libRty] putOldElem ?l:(elem = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutOldElem (a, u, true));
       Append (PutOldElem (elem, ())));
  }

let[@libRty] getOldSize ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (PutOldSize (a, u, true)))
           (PutOldSize ((ret [@d]), u, true)
           && _X (not (_F (PutOldSize (a, u, true))))));
  }

let[@libRty] putOldSize ?l:(size = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutOldSize (a, u, true));
       Append (PutOldSize (size, ())));
  }

(* Element size operations *)
let[@libRty] getSize ?l:(elem = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: int]);
    eff =
      Admit
        (_U
           (not (PutSize ((elem [@d]), a, u, true)))
           (PutSize ((elem [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutSize ((elem [@d]), a, u, true))))));
  }

let[@libRty] putSize ?l:(elem = (true : [%v: Elem.t]))
    ?l:(size = (true : [%v: int])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutSize ((elem [@d]), b, u, true));
       Append (PutSize (elem, size, ())));
  }
