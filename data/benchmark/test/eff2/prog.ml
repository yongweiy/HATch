val put : eff:int -> unit
val get : eff:int -> int

let hd =
  ({
     retc = (fun (v : int) -> false);
     put = (fun (k : unit -> int) (_ : int) -> k ());
     get = (fun (k : int -> int) (i : int) -> k i);
   }
    : hd:int -> bool)

let x =
  match_with 1
    ({
       retc = (fun (v : int) -> v);
       put = (fun (k : unit -> int) (_ : int) -> k ());
       get = (fun (k : int -> int) (i : int) -> k i);
     }
      : hd:int -> int)