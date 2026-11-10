(* Event handling *)
val hasNextEvent : unit -> bool
val getEventTarget : unit -> Elem.t
val getEventType : unit -> int
val nextEvent : unit -> unit
val addEvent : int -> Elem.t -> unit

(* Element state tracking *)
val hasOldElem : unit -> bool
val getOldElem : unit -> Elem.t
val putOldElem : Elem.t -> unit
val getOldSize : unit -> int
val putOldSize : int -> unit

(* Element size operations *)
val getSize : Elem.t -> int
val putSize : Elem.t -> int -> unit
