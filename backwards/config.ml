open Language
open Rty

type config = {
  rctx : RTypectx.ctx;
  eff : Eff.t;
  sfa : Sft.sft;
  width : int;
  steps : int;
  path : Eff.t;  (* Track the execution path for incorrectness witness *)
}
(** [width] remembers the shortest distance from [sfa.init] to one of
    its final state(s); [steps] remembers the number of (backwards)
    steppings takend to reach the current configuration. *)

(** configurations with "narrower" [sfa] and less [steps] should be
    prioritized; in particular, when more [steps] have been taken, a
    "narrower" [sfa] is preferred. *)
let create_worklist ~init_width = Pairing_heap.create ~min_size:20 ~cmp:(fun c1 c2 ->
  (* Dynamic weighing: exploration weight decreases as steps increase *)
  let exploration_weight = max 0.1 (1.0 /. (1.0 +. float_of_int (max c1.steps c2.steps))) in
  let exploitation_weight = 1.0 -. exploration_weight in
  
  (* Measure exploitation by distance from initial width *)
  let exploitation1 = float_of_int (init_width - c1.width) in
  let exploitation2 = float_of_int (init_width - c2.width) in
  
  (* Normalize steps for fair comparison *)
  let max_steps = max c1.steps c2.steps in
  let norm_steps1 = if max_steps = 0 then 0.0 else float_of_int c1.steps /. float_of_int max_steps in
  let norm_steps2 = if max_steps = 0 then 0.0 else float_of_int c2.steps /. float_of_int max_steps in
  
  (* Weighted score: lower is better (negative exploitation means higher exploitation is better) *)
  let score1 = (-.exploitation_weight) *. exploitation1 +. exploration_weight *. norm_steps1 in
  let score2 = (-.exploitation_weight) *. exploitation2 +. exploration_weight *. norm_steps2 in
  
  Float.compare score1 score2) ()

include Pairing_heap
