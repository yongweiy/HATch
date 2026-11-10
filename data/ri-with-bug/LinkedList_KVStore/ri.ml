let[@pred] rI (a1: Ptr.t) (a2: Ptr.t) =
  _G (not (PutNext(n1, n2, v, not (n1 == a1) && n2 == a2)))
  || (_U
        (not (PutNext(n1, n2, v, not (n1 == a1) && n2 == a2)))
        (PutNext ((a1 [@d]), n2, v, not (n2 == a2))))
