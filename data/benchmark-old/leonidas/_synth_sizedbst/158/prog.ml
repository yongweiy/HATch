let rec goal (d : int) (s0 : int) (lo : int) (hi : int) =
  (if lt_eq_one lo
   then Node ((increment hi), Leaf, Leaf)
   else Node ((increment lo), Leaf, Leaf) : int tree)