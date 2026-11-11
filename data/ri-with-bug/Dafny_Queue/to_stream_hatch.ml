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
   history, which is wrong for to_stream.ml's consuming GetChar's.
   Reachability reading (srlexec reach_mode): a witness ends outside [post],
   i.e. the stream, initially empty (AtEOS (s, true)), starts with h then i,
   i <> h (GetChar (s, h); GetChar (s, i)). *)
let[@assertRty] write_chars ((h : Char.t) [@ghost]) ((i : Char.t) [@ghost])
    ?l:(q = (true : [%v: Queue.t])) ?l:(s = (true : [%v: Stream.t])) =
  {
    pre = _G (not (PutChar ((s [@d]), b, u, true)));
    res = (true : [%v: unit]);
    post =
      not
        (_U
           (not (PutChar ((s [@d]), b, u, true)))
           (PutChar ((s [@d]), (h [@d]), u, true)
           && _X
                (_U
                   (not (PutChar ((s [@d]), b, u, true)))
                   (PutChar ((s [@d]), (i [@d]), u, not (i == h))))));
  }
