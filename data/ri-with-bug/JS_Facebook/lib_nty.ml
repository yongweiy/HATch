(* DOM node operations *)
val getClassName : Node.t -> int
val setClassName : Node.t -> int -> unit
val getNodeId : Node.t -> int
val setNodeId : Node.t -> int -> unit
val getChildren : Node.t -> Iterator.t
val addChild : Node.t -> Node.t -> unit

(* DOM tree traversal *)
val findByClass : Node.t -> int -> Node.t

(* Iterator operations *)
val hasNext : Iterator.t -> bool
val next : Iterator.t -> Node.t

(* Contact store operations *)
val putContact : int -> int -> unit
val getContact : int -> int
val memContact : int -> bool
