(* HATch-format counterpart of lib_rty.ml (append-only history, every call is
   logged; see data/ri-with-bug/HATCH_SPECS.md).

   Event queue: lib_rty.ml's nextEvent [Reject]s (dequeues) the oldest
   AddEvent.  Here the queue is FIFO by position: after k NextEvent's, the head
   is the (k+1)-th AddEvent and the queue is non-empty iff there are more than
   k AddEvent's.  This is exact for up to 2 consumed events; histories with
   more NextEvent's satisfy no case of hasNextEvent/getEventTarget/getEventType,
   i.e. the spec under-approximates, so any HATch witness is genuine. *)

let[@libRty] addEvent ?l:(typ = (true : [%v: int])) ?l:(target = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddEvent ((typ [@d]), (target [@d]), v, true);
  }

let[@libRty] hasNextEvent ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre =
        (_G (not (NextEvent (x_0, u, true))) && _F (AddEvent (a, b, u, true)))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))) && _F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true)))))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))))) && _F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true)))))));
      res = (v : [%v: bool]);
      newadding = lastL && HasNextEvent (x_0, v, v);
    };
    {
      pre =
        (_G (not (NextEvent (x_0, u, true))) && _G (not (AddEvent (a, b, u, true))))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))) && not (_F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true))))))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))))) && not (_F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true) && _X (_F (AddEvent (a, b, u, true))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNextEvent (x_0, v, not v);
    };
  |]

let[@libRty] getEventType ((typ : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre =
      (_G (not (NextEvent (x_0, u, true))) && _U (not (AddEvent (a, b, u, true))) (AddEvent ((typ [@d]), b, u, true)))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))) && _U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent ((typ [@d]), b, u, true)))))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))))) && _U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent ((typ [@d]), b, u, true)))))));
    res = (v == typ : [%v: int]);
    newadding = lastL && GetEventType (x_0, v, v == typ);
  }

let[@libRty] getEventTarget ((target : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre =
      (_G (not (NextEvent (x_0, u, true))) && _U (not (AddEvent (a, b, u, true))) (AddEvent (a, (target [@d]), u, true)))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))) && _U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent (a, (target [@d]), u, true)))))
      || (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_U (not (NextEvent (x_0, u, true))) (NextEvent (x_0, u, true) && _X (_G (not (NextEvent (x_0, u, true))))))) && _U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent (a, b, u, true) && _X (_U (not (AddEvent (a, b, u, true))) (AddEvent (a, (target [@d]), u, true)))))));
    res = (v == target : [%v: Elem.t]);
    newadding = lastL && GetEventTarget (x_0, v, v == target);
  }

let[@libRty] nextEvent ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && NextEvent (x_0, v, true);
  }

let[@libRty] putOldElem ?l:(elem = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutOldElem ((elem [@d]), v, true);
  }

let[@libRty] hasOldElem ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre = _F (PutOldElem (x_0, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasOldElem (x_0, v, v);
    };
    {
      pre = not (_F (PutOldElem (x_0, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasOldElem (x_0, v, not v);
    };
  |]

(* last write wins (lib_rty.ml's putOldElem Rejects the previous one) *)
let[@libRty] getOldElem ((elem : Elem.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre =
      _F
        (PutOldElem ((elem [@d]), u, true)
        && _X (_G (not (PutOldElem (a, u, true)))));
    res = (v == elem : [%v: Elem.t]);
    newadding = lastL && GetOldElem (x_0, v, v == elem);
  }

let[@libRty] putOldSize ?l:(size = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutOldSize ((size [@d]), v, true);
  }

let[@libRty] getOldSize ((size : int) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre =
      _F
        (PutOldSize ((size [@d]), u, true)
        && _X (_G (not (PutOldSize (a, u, true)))));
    res = (v == size : [%v: int]);
    newadding = lastL && GetOldSize (x_0, v, v == size);
  }

let[@libRty] putSize ?l:(elem = (true : [%v: Elem.t])) ?l:(size = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutSize ((elem [@d]), (size [@d]), v, true);
  }

let[@libRty] getSize ((size : int) [@ghost]) ?l:(elem = (true : [%v: Elem.t])) =
  {
    pre =
      _F
        (PutSize ((elem [@d]), (size [@d]), u, true)
        && _X (_G (not (PutSize ((elem [@d]), b, u, true)))));
    res = (v == size : [%v: int]);
    newadding = lastL && GetSize ((elem [@d]), v, v == size);
  }
