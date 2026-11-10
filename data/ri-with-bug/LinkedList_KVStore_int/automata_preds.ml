let[@pred] nextP (a : int) (b : int) =
  _F (PutNext ((a [@d]), (b [@d]), u, true) &&
        _X (_G (not (PutNext ((a [@d]), c, u, true)))))

let[@pred] valP (a : int) (v : Elem.t) =
  _F (PutVal ((a [@d]), (v [@d]), u, true) &&
        _X (_G (not (PutVal ((a [@d]), v, u, true)))))
