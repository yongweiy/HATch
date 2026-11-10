let rec write_chars (q : Queue.t) (s : Stream.t) : unit =
  if isEmpty q then ()
  else
    let (c : Char.t) = take q in
    putChar s c;
    write_chars q s;
    ()

(* HATch baseline only (scripts/run_paper_benchmarks.py HATCH_CLIENT_OVERRIDE).
   Same program and query as to_stream.ml, but the query is written as an
   Htriple directly: Constrain_to_htriple conjoins sequential events over one
   history, which is wrong for to_stream.ml's five consuming GetChar's.
   Reachability reading (srlexec reach_mode): a witness ends outside [post],
   i.e. the stream, initially empty (AtEOS (s, true)), starts with
   h, e, ll, ll, o (GetChar (s, h); GetChar (s, e); GetChar (s, l);
   GetChar (s, l); GetChar (s, o)). *)
let[@assertRty] write_chars ((h : Char.t) [@ghost]) ((e : Char.t) [@ghost])
    ((ll : Char.t) [@ghost]) ((o : Char.t) [@ghost])
    ?l:(q = (true : [%v: Queue.t])) ?l:(s = (true : [%v: Stream.t])) =
  {
    pre = _G (not (PutChar ((s [@d]), b, u, true)));
    res = (true : [%v: unit]);
    post =
      not
        (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (h [@d]), u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (e [@d]), u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (ll [@d]), u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (ll [@d]), u, true) && _X (_U (not (PutChar ((s [@d]), b, u, true))) (PutChar ((s [@d]), (o [@d]), u, true)))))))))));
  }
