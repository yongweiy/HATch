let[@libRty] isEmpty ?l:(q = (true : [%v: Queue.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_G (not (Add ((q [@d]), a, u, true))))),
          (Guard (not ret);
           Admit (_F (Add ((q [@d]), a, u, true)))) );
  }

let[@libRty] add ?l:(q = (true : [%v: Queue.t]))
    ?l:(a = (true : [%v: Char.t])) =
  { ret = (true : [%v: unit]); eff = Append (Add (q, a, ())) }

let[@libRty] take ?l:(q = (true : [%v: Queue.t])) =
  {
    ret = (true : [%v: Char.t]);
    eff =
      (Admit
         (_U
            (not (Add ((q [@d]), a, u, true)))
            (Add ((q [@d]), (ret [@d]), u, true)));
       Reject (Add ((q [@d]), (ret [@d]), u, true)));
  }

let[@libRty] atEOS ?l:(s = (true : [%v: Stream.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit (_G (not (PutChar ((s [@d]), a, u, true))))),
          (Guard (not ret);
           Admit (_F (PutChar ((s [@d]), a, u, true)))) );
  }

let[@libRty] putChar ?l:(s = (true : [%v: Stream.t]))
    ?l:(c = (true : [%v: Char.t])) =
  { ret = (true : [%v: unit]); eff = Append (PutChar (s, c, ())) }

let[@libRty] getChar ?l:(s = (true : [%v: Stream.t])) =
  {
    ret = (true : [%v: Char.t]);
    eff =
      (Admit
         (_U
            (not (PutChar ((s [@d]), a, u, true)))
            (PutChar ((s [@d]), (ret [@d]), u, true)));
       Reject (PutChar ((s [@d]), (ret [@d]), u, true)));
  }
