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
let worklist = Pairing_heap.create ~min_size:20 ~cmp:_ ()

include Pairing_heap
