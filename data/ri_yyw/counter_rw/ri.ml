(* let[@pred] rI (c : int) = writtenP c *)
let[@pred] rI = _F (Write (x, v, (x > 0)) && _X (_G (not (Write (x_0, v, true)))))
