open Language

type 'a t = Found of RTypectx.ctx * Rty.Sft.sft * 'a | Fail | Go of 'a

(** Monad interface for Incor.t *)

let return x = Go x

let bind m f =
  match m with
  | Found (rctx, sft, x) -> Found (rctx, sft, x)  (* Found is terminal *)
  | Fail -> Fail  (* Fail is terminal *)
  | Go x -> f x  (* Continue with the computation *)

let map f m =
  match m with
  | Found (rctx, sft, x) -> Found (rctx, sft, f x)
  | Fail -> Fail
  | Go x -> Go (f x)

let ( >>= ) = bind
let ( >>| ) = Fun.flip map
let ( let* ) m f = bind m f
let ( let+ ) m f = map f m

(** Additional utility functions *)

let found rctx sft x = Found (rctx, sft, x)
let fail = Fail
let go x = Go x

let is_found = function
  | Found _ -> true
  | _ -> false

let is_fail = function
  | Fail -> true
  | _ -> false

let is_go = function
  | Go _ -> true
  | _ -> false

let extract = function
  | Found (rctx, sft, x) -> Some (rctx, sft, x)
  | _ -> None

let extract_go = function
  | Go x -> Some x
  | _ -> None

