let[@pred] rI (s1 : Node.t) (s2 : Node.t) =
  _G
    (AddNode ((s1 [@d]), c, v, true) && AddNode ((s2 [@d]), c, v, true))
    #==> (is_connected s1 s2)
