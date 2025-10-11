val ( || ) : bool -> bool -> bool
val ( && ) : bool -> bool -> bool

(* == is poly *)
val ( == ) : int -> int -> bool
val ( != ) : int -> int -> bool
val ( < ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int
val ( * ) : int -> int -> int
val ( / ) : int -> int -> int
val not : bool -> bool

(* path *)
val parent : Path.t -> Path.t
val is_root : Path.t -> bool

(* bytes *)
val is_del : Bytes.t -> bool
val is_dir : Bytes.t -> bool
val add_child : Bytes.t -> Path.t -> Bytes.t
val del_child : Bytes.t -> Path.t -> Bytes.t
val is_child : Bytes.t -> Path.t -> bool
val has_child : Bytes.t -> bool

(* elem *)
val elem_lt : Elem.t -> Elem.t -> bool
val elem_eq : Elem.t -> Elem.t -> bool

(* color *)
val color_eq : Color.t -> Color.t -> bool

(* node *)
val node_eq : Node.t -> Node.t -> bool

(* cell *)
val cell_eq : Cell.t -> Cell.t -> bool

(* pointer *)
val ptr_eq : Ptr.t -> Ptr.t -> bool
val is_nullptr : Ptr.t -> bool
val get_nullptr : unit -> Ptr.t

(* eff operator **)

(* set *)
val set_insert : int -> unit
val set_mem : int -> bool
val is_empty : NodeSet.t -> bool
val mem_node : Node.t -> NodeSet.t -> bool
val add_node : Node.t -> NodeSet.t -> NodeSet.t
val del_node : Node.t -> NodeSet.t -> NodeSet.t

(* val nil : unit -> NodeList.t *)
(* val cons : Node.t -> NodeList.t -> NodeList.t *)
val is_nil : NodeList.t -> bool
val hd : NodeList.t -> Node.t
val tl : NodeList.t -> NodeList.t
                         
(* tree *)
val is_leaf : NodeTree.t -> bool
val is_node : Node.t -> NodeTree.t -> bool
val node : NodeTree.t -> Node.t
val is_left : NodeTree.t -> NodeTree.t -> bool
val left : NodeTree.t -> NodeTree.t
val is_right : NodeTree.t -> NodeTree.t -> bool
val right : NodeTree.t -> NodeTree.t
val mk_leaf : unit -> NodeTree.t
val mk_tree : Node.t -> NodeTree.t -> NodeTree.t -> NodeTree.t
