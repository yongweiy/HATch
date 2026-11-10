val put : Path.t -> Bytes.t -> unit
val get : Path.t -> Bytes.t
val del : Path.t -> unit
val exists : Path.t -> bool
val getParent : Path.t -> Path.t
val isRoot : Path.t -> bool

val isDir : Bytes.t -> bool
val addChild : Bytes.t -> Path.t -> unit
val memChild : Bytes.t -> Path.t -> bool
val delChild : Bytes.t -> Path.t -> unit
val getChildren : Bytes.t -> PathList.t
