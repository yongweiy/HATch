(* HATch-format counterpart of lib_rty.ml (append-only history, every call is
   logged; see data/ri-with-bug/HATCH_SPECS.md).  The positional formulas are
   mechanical (one disjunct per k = 0..5); keep the queue and stream halves in
   sync.

   lib_rty.ml's take / getChar Reject (dequeue) the oldest Add / PutChar.
   Here both are FIFO by position: after k Take's (GetChar's) the head is the
   (k+1)-th Add (PutChar) and the queue (stream) is empty iff there are no
   more than k of them.  Exact for up to 5 dequeued elements, values may
   repeat; histories with more dequeues satisfy no case (under-approximation,
   so HATch witnesses stay genuine). *)

let[@libRty] isEmpty ?l:(q = (true : [%v: Queue.t])) =
  [|
    {
      pre =
        (_G (not (Take ((q [@d]), y, true))) && not (_F (Add ((q [@d]), b, u, true))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))) && not (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))) && not (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true))))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))) && not (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true))))))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))) && not (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true))))))))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))))) && not (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true))))))))))))));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, v);
    };
    {
      pre =
        (_G (not (Take ((q [@d]), y, true))) && _F (Add ((q [@d]), b, u, true)))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))) && _F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true)))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))) && _F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true)))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))) && _F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true)))))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))) && _F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true)))))))))))
      || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))))) && _F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true) && _X (_F (Add ((q [@d]), b, u, true)))))))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((q [@d]), v, not v);
    };
  |]

let[@libRty] add ?l:(q = (true : [%v: Queue.t])) ?l:(c = (true : [%v: Char.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Add ((q [@d]), (c [@d]), v, true);
  }

let[@libRty] take ((c : Char.t) [@ghost]) ?l:(q = (true : [%v: Queue.t])) =
  {
    pre =
      (_G (not (Take ((q [@d]), y, true))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))
    || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))))
    || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))))))
    || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))))))))
    || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))))))))))
    || (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_U (not (Take ((q [@d]), y, true))) (Take ((q [@d]), y, true) && _X (_G (not (Take ((q [@d]), y, true))))))))))))) && _U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), b, u, true) && _X (_U (not (Add ((q [@d]), b, u, true))) (Add ((q [@d]), (c [@d]), u, true)))))))))))));
    res = (v == c : [%v: Char.t]);
    newadding = lastL && Take ((q [@d]), v, v == c);
  }

let[@libRty] atEOS ?l:(s = (true : [%v: Stream.t])) =
  [|
    {
      pre =
        (_G (not (GetChar ((s [@d]), y, true))) && not (_F (PutChar ((s [@d]), b, u, true))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))) && not (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))) && not (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true))))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))) && not (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true))))))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))) && not (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true))))))))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))))) && not (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true))))))))))))));
      res = (v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, v);
    };
    {
      pre =
        (_G (not (GetChar ((s [@d]), y, true))) && _F (PutChar ((s [@d]), b, u, true)))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))) && _F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true)))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))) && _F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true)))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))) && _F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true)))))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))) && _F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true)))))))))))
      || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))))) && _F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true) && _X (_F (PutChar ((s [@d]), b, u, true)))))))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && AtEOS ((s [@d]), v, not v);
    };
  |]

let[@libRty] putChar ?l:(s = (true : [%v: Stream.t])) ?l:(c = (true : [%v: Char.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutChar ((s [@d]), (c [@d]), v, true);
  }

let[@libRty] getChar ((c : Char.t) [@ghost]) ?l:(s = (true : [%v: Stream.t])) =
  {
    pre =
      (_G (not (GetChar ((s [@d]), y, true))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))
    || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))))
    || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))))))
    || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))))))))
    || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))))))))))
    || (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_U (not (GetChar ((s [@d]), y, true))) (GetChar ((s [@d]), y, true) && _X (_G (not (GetChar ((s [@d]), y, true))))))))))))) && _U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), b, u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (c [@d]), u, true)))))))))))));
    res = (v == c : [%v: Char.t]);
    newadding = lastL && GetChar ((s [@d]), v, v == c);
  }
