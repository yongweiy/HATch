val isEmpty : unit -> bool
val add : Node.t -> unit
val take : unit -> Node.t

val connect : Node.t -> Node.t -> unit
val getNeighbors : Node.t -> NodeList.t

(* Distance/visited tracking *)
val initVisited : unit -> unit
val markVisited : Node.t -> unit
val isVisited : Node.t -> bool

