let[@libRty] ( && ) ?l:(a = (true : [%v: bool]) [@over])
    ?l:(b = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (a && b)

let[@libRty] ( || ) ?l:(a = (true : [%v: bool]) [@over])
    ?l:(b = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (a || b)

let[@libRty] not ?l:(a = (true : [%v: bool]) [@over]) : [%v: bool] =
  iff v (not a)

let[@libRty] ( == ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] ( != ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a != b)

let[@libRty] ( < ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a < b)

let[@libRty] ( > ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a > b)

let[@libRty] ( <= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a <= b)

let[@libRty] ( >= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  iff v (a >= b)

let[@libRty] ( + ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + b

let[@libRty] ( - ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a - b

let[@libRty] ( mod ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a mod b

let[@libRty] ( * ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a * b

let[@libRty] ( / ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (not (v == 0) : [%v: int]) [@over]) : [%v: int] =
  v == a / b

let[@libRty] key_eq ?l:(a = (true : [%v: Key.t]) [@over])
    ?l:(b = (true : [%v: Key.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] elem_eq ?l:(a = (true : [%v: Elem.t]) [@over])
    ?l:(b = (true : [%v: Elem.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] elem_lt ?l:(a = (true : [%v: Elem.t]) [@over])
    ?l:(b = (true : [%v: Elem.t]) [@over]) : [%v: bool] =
  iff v (elem_lt a b)

let[@libRty] color_eq ?l:(a = (true : [%v: Color.t]) [@over])
    ?l:(b = (true : [%v: Color.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] node_eq ?l:(a = (true : [%v: Node.t]) [@over])
    ?l:(b = (true : [%v: Node.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] cell_eq ?l:(a = (true : [%v: Cell.t]) [@over])
    ?l:(b = (true : [%v: Cell.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] ptr_eq ?l:(a = (true : [%v: Ptr.t]) [@over])
    ?l:(b = (true : [%v: Ptr.t]) [@over]) : [%v: bool] =
  iff v (a == b)

let[@libRty] is_nullptr ?l:(a = (true : [%v: Ptr.t]) [@over]) : [%v: bool] =
  iff v (is_nullptr a)

let[@libRty] get_nullptr ?l:(a = (true : [%v: unit]) [@over]) : [%v: Ptr.t] =
  is_nullptr v

let[@libRty] mem_node ?l:(a = (true : [%v: Node.t]) [@over])
    ?l:(s = (true : [%v: NodeSet.t]) [@over]) : [%v: bool] =
  iff v (mem_node a s)

let[@libRty] add_node ?l:(a = (true : [%v: Node.t]) [@over])
    ?l:(s = (true : [%v: NodeSet.t]) [@over]) : [%v: NodeSet.t] =
  v == add_node a s

let[@libRty] del_node ?l:(a = (true : [%v: Node.t]) [@over])
    ?l:(s = (true : [%v: NodeSet.t]) [@over]) : [%v: NodeSet.t] =
  v == del_node a s

let[@libRty] is_empty ?l:(s = (true : [%v: NodeSet.t]) [@over]) : [%v: bool] =
  iff v (is_empty s)

(* let[@libRty] nil ?l:(u = (true : [%v: unit])) : [%v: NodeList.t] = v == nil () *)

(* let[@libRty] cons ?l:(hd = (true : [%v: Node.t])) *)
(*     ?l:(tl = (true : [%v: NodeList.t])) : [%v: NodeList.t] = *)
(*   v == cons hd tl *)

(* let[@libRty] is_nil ?l:(xs = (true : [%v: NodeList.t]) [@over]) : [%v: bool] = *)
(*   iff v (xs == nil ()) *)

(* let[@libRty] hd ?l:(xs = (not (v == nil ()) : [%v: NodeList.t]) [@over]) : *)
(*     [%v: Node.t] = *)
(*   v == hd xs *)

(* let[@libRty] tl ?l:(xs = (not (v == nil ()) : [%v: NodeList.t]) [@over]) : *)
(*     [%v: NodeList.t] = *)
(*   v == tl xs *)

let[@libRty] is_nil ?l:(xs = (true : [%v: NodeList.t]) [@over]) : [%v: bool] =
  iff v (is_nil xs)

let[@libRty] hd ?l:(xs = (not (is_nil v) : [%v: NodeList.t]) [@over]) :
    [%v: Node.t] =
  v == hd xs

let[@libRty] tl ?l:(xs = (not (is_nil v) : [%v: NodeList.t]) [@over]) :
    [%v: NodeList.t] =
  v == tl xs

let[@libRty] is_leaf ?l:(x = (true : [%v: NodeTree.t]) [@over]) : [%v: bool] =
  iff v (is_leaf x)

let[@libRty] is_node ?l:(n = (true : [%v: Node.t]) [@over])
    ?l:(x = (true : [%v: NodeTree.t]) [@over]) : [%v: bool] =
  is_node n x

let[@libRty] node ?l:(x = (true : [%v: NodeTree.t]) [@over]) : [%v: Node.t] =
  is_node v x

let[@libRty] is_left ?l:(y = (true : [%v: NodeTree.t]) [@over])
    ?l:(x = (true : [%v: NodeTree.t]) [@over]) : [%v: bool] =
  is_left y x

let[@libRty] left ?l:(x = (true : [%v: NodeTree.t]) [@over]) :
    [%v: NodeTree.t] =
  is_left v x

let[@libRty] is_right ?l:(y = (true : [%v: NodeTree.t]) [@over])
    ?l:(x = (true : [%v: NodeTree.t]) [@over]) : [%v: bool] =
  is_right y x

let[@libRty] right ?l:(x = (true : [%v: NodeTree.t]) [@over]) :
    [%v: NodeTree.t] =
  is_right v x

let[@libRty] mk_tree ?l:(n = (true : [%v: Node.t]) [@over])
    ?l:(lt = (true : [%v: NodeTree.t]) [@over])
    ?l:(rt = (true : [%v: NodeTree.t]) [@over]) : [%v: NodeTree.t] =
  is_node n v && is_left lt v && is_right rt v

let[@libRty] mk_leaf ?l:(u = (true : [%v: unit]) [@over]) : [%v: NodeTree.t] =
  is_leaf v
