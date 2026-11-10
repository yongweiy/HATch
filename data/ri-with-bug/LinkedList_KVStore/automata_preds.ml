let[@pred] nextP (a : Ptr.t) (b : Ptr.t) =
  _F (PutNext ((a [@d]), (b [@d]), u, true) &&
        _X (_G (not (PutNext ((a [@d]), c, u, true)))))

let[@pred] valP (a : Ptr.t) (v : Elem.t) =
  _F (PutVal ((a [@d]), (v [@d]), u, true) &&
        _X (_G (not (PutVal ((a [@d]), v, u, true)))))

let[@pred] notvalP (a : Ptr.t) (v : Elem.t) =
  _F (PutVal ((a [@d]), w, u, not (elem_eq w v)) &&
        _X (_G (not (PutVal ((a [@d]), v, u, true)))))
