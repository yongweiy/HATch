val create : unit -> Set.t
val add : Elem.t -> Set.t -> unit
val mem : Elem.t -> Set.t -> bool
val isEmpty : Set.t -> bool
val getIter : Set.t -> Iter.t
val hasIter : Iter.t -> Set.t -> bool
val next : Iter.t -> Elem.t
val hasNext : Iter.t -> bool
