let[@pred] writtenP (idx : int) =
  _F (Write ((idx [@d]), v, true) && _X (_G (not (Write (x_0, v, true)))))
