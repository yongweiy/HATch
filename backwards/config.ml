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
  (* Dynamic weighing: exploration weight decreases as steps increase *)
  let exploration_weight = max 0.1 (1.0 /. (1.0 +. float_of_int (max c1.steps c2.steps))) in
  let exploitation_weight = 1.0 -. exploration_weight in
  
  (* Normalize metrics to [0,1] range for fair comparison *)
  let max_width = max c1.width c2.width in
  let norm_width1 = if max_width = 0 then 0.0 else float_of_int c1.width /. float_of_int max_width in
  let norm_width2 = if max_width = 0 then 0.0 else float_of_int c2.width /. float_of_int max_width in
  
  let max_steps = max c1.steps c2.steps in
  let norm_steps1 = if max_steps = 0 then 0.0 else float_of_int c1.steps /. float_of_int max_steps in
  let norm_steps2 = if max_steps = 0 then 0.0 else float_of_int c2.steps /. float_of_int max_steps in
  
  (* Weighted score: lower is better *)
  let score1 = exploitation_weight *. norm_width1 +. exploration_weight *. norm_steps1 in
  let score2 = exploitation_weight *. norm_width2 +. exploration_weight *. norm_steps2 in
  
  Float.compare score1 score2) ()

include Pairing_heap
