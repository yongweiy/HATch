open Language
open Rty

(** Configuration for backward search *)
type backward_config = {
  rctx : RTypectx.ctx;
  eff : Eff.t;  (* Remaining effect to process *)
  sfa : Sft.sft;  (* Current automaton state *)
  width : int;
  steps : int;
  path : Eff.t;  (* Execution path for witness *)
}

(** Configuration for forward search *)
type forward_config = {
  rctx : RTypectx.ctx;
  eff : Eff.t;  (* Remaining effect to process *)
  sfa : Sft.sft;  (* Current automaton state *)
  width : int;
  steps : int;
  path : Eff.t;  (* Execution path for witness *)
}

(** Unified configuration that can be either forward or backward *)
type direction = Forward | Backward

type config = {
  dir : direction;
  rctx : RTypectx.ctx;
  eff : Eff.t;
  sfa : Sft.sft;
  width : int;
  steps : int;
  path : Eff.t;
}

(** Create a backward configuration *)
let mk_backward rctx eff sfa width steps path =
  { dir = Backward; rctx; eff; sfa; width; steps; path }

(** Create a forward configuration *)
let mk_forward rctx eff sfa width steps path =
  { dir = Forward; rctx; eff; sfa; width; steps; path }

(** Worklist for backward search *)
let create_backward_worklist ~init_width =
  Pairing_heap.create ~min_size:20
    ~cmp:(fun c1 c2 ->
      (* Use the same lexicographic strategy as backwards/ *)
      match Int.compare (Rty.depth_of_eff c1.eff) (Rty.depth_of_eff c2.eff) with
      | 0 ->
          Int.compare
            (Sft.emptiness_check_difficuly_of c1.sfa / (c1.width + 1))
            (Sft.emptiness_check_difficuly_of c2.sfa / (c2.width + 1))
      | cmp -> cmp)
    ()

(** Worklist for forward search *)
let create_forward_worklist ~init_width =
  Pairing_heap.create ~min_size:20
    ~cmp:(fun c1 c2 ->
      (* For forward search, prioritize by effect depth (prefer to consume effect) *)
      match Int.compare (Rty.depth_of_eff c2.eff) (Rty.depth_of_eff c1.eff) with
      | 0 ->
          Int.compare
            (Sft.emptiness_check_difficuly_of c1.sfa / (c1.width + 1))
            (Sft.emptiness_check_difficuly_of c2.sfa / (c2.width + 1))
      | cmp -> cmp)
    ()

include Pairing_heap

