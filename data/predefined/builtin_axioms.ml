let[@axiom] bytes2 ((content [@forall]) : Bytes.t) =
  not (is_dir content && is_del content)

let[@axiom] path1 ((path [@forall]) : Path.t) = not (path == parent path)

let[@axiom] elem1 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b || elem_lt b a) (not (a == b))

let[@axiom] elem2 ((a [@forall]) : Elem.t) = not (elem_lt a a)

let[@axiom] elem3 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies (elem_lt a b) (not (elem_lt b a))

let[@axiom] elem4 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t)
    ((c [@forall]) : Elem.t) =
  implies (elem_lt a b && elem_lt b c) (elem_lt a c)

let[@axiom] elem5 ((a [@forall]) : Elem.t) ((b [@forall]) : Elem.t) =
  implies ((not (elem_lt a b)) && not (elem_lt b a)) (a == b)

let[@axiom] ptr1 ((a [@forall]) : Ptr.t) ((b [@forall]) : Ptr.t) =
  implies (is_nullptr a && a == b) (is_nullptr b)

let[@axiom] ptr2 ((a [@forall]) : Ptr.t) ((b [@forall]) : Ptr.t) =
  implies (is_nullptr a && not (a == b)) (not (is_nullptr b))

(* let[@axiom] set1 ((a [@forall]) : Node.t) ((s [@forall]) : NodeSet.t) = *)
(*   implies (is_empty s) (not (mem_node a s)) *)

(* let[@axiom] set2 ((a [@forall]) : Node.t) ((b [@forall]) : Node.t) *)
(*     ((s [@forall]) : NodeSet.t) = *)
(*   ite (a == b) *)
(*     (not (mem_node a (del_node b s))) *)
(*     (iff (mem_node a (del_node b s)) (mem_node a s)) *)

(* let[@axiom] set3 ((a [@forall]) : Node.t) ((b [@forall]) : Node.t) *)
(*     ((s [@forall]) : NodeSet.t) = *)
(*   ite (a == b) *)
(*     (mem_node a (add_node b s)) *)
(*     (iff (mem_node a (add_node b s)) (mem_node a s)) *)

(* let[@axiom] list1 ((hd [@forall]) : Node.t) ((tl [@forall]) : NodeList.t) = *)
(*   not (nil () == cons hd tl) *)

(* let[@axiom] list2 ((hd1 [@forall]) : Node.t) ((tl1 [@forall]) : NodeList.t) *)
(*     ((hd2 [@forall]) : Node.t) ((tl2 [@forall]) : NodeList.t) = *)
(*   implies (cons hd1 tl1 == cons hd2 tl2) (hd1 == hd2 && tl1 == tl2) *)

(* let[@axiom] list3 ((xs [@forall]) : NodeList.t) = *)
(*   xs == nil () || fun ((hd [@exists]) : Node.t) ((tl [@exists]) : NodeList.t) -> *)
(*   xs == cons hd tl *)

(* let[@axiom] list4 ((hd [@forall]) : Node.t) ((tl [@forall]) : NodeList.t) = *)
(*   hd (cons hd tl) == hd *)

(* let[@axiom] list5 ((hd [@forall]) : Node.t) ((tl [@forall]) : NodeList.t) = *)
(*   tl (cons hd tl) == tl *)

let[@axiom] tree1 ((n [@forall]) : Node.t) ((t [@forall]) : NodeTree.t) =
  implies (is_node n t) (not (is_leaf t))

let[@axiom] tree2 ((l [@forall]) : NodeTree.t) ((t [@forall]) : NodeTree.t) =
  implies (is_left l t) (not (is_leaf t))

let[@axiom] tree3 ((r [@forall]) : NodeTree.t) ((t [@forall]) : NodeTree.t) =
  implies (is_right r t) (not (is_leaf t))

let[@axiom] tree4 ((a [@forall]) : NodeTree.t) ((b [@forall]) : NodeTree.t) =
  implies (is_leaf a && a == b) (is_leaf b)

let[@axiom] tree5 ((a [@forall]) : NodeTree.t) ((b [@forall]) : NodeTree.t) =
  implies (is_leaf a && not (a == b)) (not (is_leaf b))
