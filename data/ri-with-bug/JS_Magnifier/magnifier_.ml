let handleEvents (uu : unit) : unit =
  let magnify : Elem.t -> unit =
   fun (curr : Elem.t) ->
    let (hasOld : bool) = hasOldElem () in
    (if hasOld then
       let (old : Elem.t) = getOldElem () in
       let (oldSize : int) = getOldSize () in
       putSize old oldSize);
    putOldElem curr;
    let (currSize : int) = getSize curr in
    putOldSize currSize;
    putSize curr 30;
    ()
  in

  let rec eventLoop : unit -> unit =
   fun (u : unit) ->
    let (hasEvent : bool) = hasNextEvent () in
    if hasEvent then (
      let (target : Elem.t) = getEventTarget () in
      let (eventType : int) = getEventType () in
      nextEvent ();

      if eventType == 1 then (
        (* MouseMove *)
        magnify target;
        ())
      else ();
      eventLoop ();
      ())
  in
  eventLoop ();
  ()

let[@assertRty] handleEvents ?l:(uu = (true : [%v: unit])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (smallx : int) = (v < 30 : [%v: int]) in
       let (largex : int) = (v > 30 : [%v: int]) in
       let (x : Elem.t) = (true : [%v: Elem.t]) in
       let (smally : int) = (v < 30 : [%v: int]) in
       let (largey : int) = (v > 30 : [%v: int]) in
       let (y : Elem.t) = (not (v == x) : [%v: Elem.t]) in
       let (small : int) = (v < 30 : [%v: int]) in
       Constrain
         ( (GetSize (x, smallx);
            GetSize (y, smally);
            GetOldSize ((), small)),
           (GetSize (x, largex);
            GetSize (y, largey)) ));
  }
