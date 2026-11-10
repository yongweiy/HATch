(* Pointer operations *)
val createPtr : unit -> Ptr.t

(* Tree structure queries *)
val isLeaf : Ptr.t -> bool

(* Value KV store operations *)
val getValue : Ptr.t -> Elem.t
val setValue : Ptr.t -> Elem.t -> unit

(* Color KV store operations *)
val getColor : Ptr.t -> bool
val setColor : Ptr.t -> bool -> unit

(* Node property access *)
val getLeft : Ptr.t -> Ptr.t
val getRight : Ptr.t -> Ptr.t

(* Node structure mutation *)
val setLeft : Ptr.t -> Ptr.t -> unit
val setRight : Ptr.t -> Ptr.t -> unit

val hasLeft : Ptr.t -> bool
val hasRight : Ptr.t -> bool
