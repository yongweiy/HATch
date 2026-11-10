let[@pred] rI (a: int) (b: int) =
  _G (not (PutNext(n1, n2, v, n1 != a && n2 == b)))
  || (_U
        (not (PutNext(n1, n2, v, n1 != a && n2 == b)))
        (PutNext ((a [@d]), n2, v, n2 != b)))
