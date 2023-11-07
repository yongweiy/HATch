let[@pred] sizeP (n : int) =
  _F (Init ((n [@d]), v, true) && _X (_F (Init (x_0, v, true))))

let[@pred] valid_idxP (n : int) = _F (Init (x_0, v, n < x_0))

let[@pred] storedP (k : int) (value : Elem.t) =
  _F
    (Update ((k [@d]), (value [@d]), v, true)
    && _X (_G (not (Update ((k [@d]), x_1, v, true)))))

let[@pred] existsP (k : int) = _F (Update ((k [@d]), x_1, v, true))

let[@pred] writtenP (idx : int) =
  _F (Write ((idx [@d]), v, true) && _X (_G (not (Write (x_0, v, true)))))
