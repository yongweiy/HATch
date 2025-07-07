open Language
open TypedCoreEff
open Rty

type t = {
  rctx : RTypectx.ctx;
  eff : Eff.t;
  sfa : Sft.sft;
  width : int;
  steps : int;
}
(** [width] remembers the shortest distance from [sfa.init] to one of
    its final state(s); [steps] remembers the number of (backwards)
    steppings takend to reach the current configuration. *)

(** configurations with "narrower" [sfa] and less [steps] should be
    prioritized; in particular, when more [steps] have been taken, a
    "narrower" [sfa] is preferred. *)
let worklist = Pairing_heap.create ~min_size:20 ~cmp:(fun c1 c2 ->
  (* When both configs have taken few steps (1-2), prioritize exploration by steps *)
  if c1.steps <= 2 && c2.steps <= 2 then
    Int.compare c1.steps c2.steps
  else
    (* Otherwise, prioritize exploitation by width first, then steps *)
    let width_cmp = Int.compare c1.width c2.width in
    if width_cmp <> 0 then width_cmp
    else Int.compare c1.steps c2.steps) ()

include Pairing_heap
