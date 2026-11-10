val create : unit -> Queue.t
val isEmpty : Queue.t -> bool
val add : Node.t -> Queue.t -> unit
val take : Queue.t -> Node.t

val connect : Node.t -> Node.t -> unit
val getNeighbors : Node.t -> NodeList.t

(* Distance/visited tracking *)
val initVisited : unit -> unit
val markVisited : Node.t -> unit
val isVisited : Node.t -> bool

