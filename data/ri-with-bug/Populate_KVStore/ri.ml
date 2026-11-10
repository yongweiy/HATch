let[@pred] rI (k1: int) (k2: int) =
  implies
    (_F (Put (k, v, u, (k == k1))))
    (_U
       (not (Put (k, v, u, (k == k2))))
       (Put (k, v, u, (k == k1))))
