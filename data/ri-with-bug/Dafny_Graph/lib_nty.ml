(* Queue operations *)
val create : unit -> Queue.t
val isEmpty : Queue.t -> bool
val add : Node.t -> Queue.t -> unit
val take : Queue.t -> Node.t

(* Graph operations *)
val connect : Node.t -> Node.t -> unit
val isConnected : Node.t -> Node.t -> bool
val getNeighbors : Node.t -> Iterator.t

(* Iterator operations *)
val hasNext : Node.t -> Iterator.t -> bool
val next : Node.t -> Iterator.t -> Node.t

(* Distance/visited tracking *)
val initVisited : unit -> unit
val markVisited : Node.t -> unit
val isVisited : Node.t -> bool
