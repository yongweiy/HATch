open Language
open Rty

type config = {
  rctx : RTypectx.ctx;
  eff : Eff.t;
  sfa : Sft.sft;
  width : int;
  steps : int;
  path : Eff.t; (* Track the execution path for incorrectness witness *)
}
(** [width] remembers the shortest distance from [sfa.init] to one of
    its final state(s); [steps] remembers the number of (backwards)
    steppings taken to reach the current configuration. *)

(** configurations with "narrower" [sfa] and less [steps] should be
    prioritized; in particular, when more [steps] have been taken, a
    "narrower" [sfa] is preferred. *)
let create_worklist ~init_width =
  Pairing_heap.create ~min_size:20
    ~cmp:(fun c1 c2 ->
      (* OLD STRATEGY: Strict lexicographic (depth primary, difficulty/width secondary)

         This strategy worked best in benchmarks with unroll_bound=1.
         Prioritizes by effect depth first (explore shallow effects),
         then by difficulty/width ratio (prefer simpler automata).

         Note: Width is dynamic and changes during backward exploration,
         so it cannot be used as a primary sorting criterion.
      *)
      match Int.compare (Rty.depth_of_eff c1.eff) (Rty.depth_of_eff c2.eff) with
      | 0 ->
          Int.compare
            (Sft.emptiness_check_difficuly_of c1.sfa / (c1.width + 1))
            (Sft.emptiness_check_difficuly_of c2.sfa / (c2.width + 1))
      | cmp -> cmp

      (* OLD STRATEGY: Strict lexicographic (depth primary, difficulty/width secondary) *)
      (* match Int.compare (Rty.depth_of_eff c1.eff) (Rty.depth_of_eff c2.eff) with
      | 0 ->
          Int.compare
            (Sft.emptiness_check_difficuly_of c1.sfa / (c1.width + 1))
            (Sft.emptiness_check_difficuly_of c2.sfa / (c2.width + 1))
      | cmp -> cmp *)

      (* Strategy 7 (Hybrid DFS): DFS with simplicity bias *)
      (* Prioritize: HIGH steps (DFS), but avoid complex automata *)
      (* Score = steps * 100 - width * 10 - difficulty *)
      (* Higher score = higher priority (explore deep but prefer simple paths) *)
      (* let score1 = c1.steps * 100 - c1.width * 10 - (Sft.emptiness_check_difficuly_of c1.sfa) in
      let score2 = c2.steps * 100 - c2.width * 10 - (Sft.emptiness_check_difficuly_of c2.sfa) in
      Int.compare score2 score1 *)  (* REVERSED: higher score = higher priority *)
      (* let score c =
           (1000 * Rty.depth_of_eff c.eff)
           + (Sft.emptiness_check_difficuly_of c.sfa / (c.width + 1))
         in
         Int.compare (score c1) (score c2) *)
      (* Prioritization strategy: Handle unreachable automata (width = Int.max) specially

         When width = Int.max (no path from init to final state), the configuration
         represents an unreachable/unsatisfiable path that should be heavily deprioritized.

         Strategy:
         1. Configurations with width = Int.max are always deprioritized
         2. Among reachable configs (width < Int.max), use lexicographic ordering:
            - Primary: effect depth (lower is better - closer to base case)
            - Secondary: difficulty/width ratio (lower is better - simpler automaton)

         This ensures unreachable paths don't pollute the search space.
      *)
      (* let is_unreachable c = c.width = Int.max_int in
         match (is_unreachable c1, is_unreachable c2) with
         | true, false -> 1  (* c1 unreachable, c2 reachable -> c2 wins *)
         | false, true -> -1 (* c1 reachable, c2 unreachable -> c1 wins *)
         | true, true ->
             (* Both unreachable: compare by depth only (try to reduce depth anyway) *)
             Int.compare (Rty.depth_of_eff c1.eff) (Rty.depth_of_eff c2.eff)
         | false, false ->
             Both reachable: lexicographic (depth primary, difficulty/width secondary) *)
             (* match Int.compare (Rty.depth_of_eff c1.eff) (Rty.depth_of_eff c2.eff) with
             | 0 ->
                 (* Same depth: prefer simpler automaton relative to width *)
                 Int.compare
                   (Sft.emptiness_check_difficuly_of c2.sfa / (c2.width + 1))
                   (Sft.emptiness_check_difficuly_of c1.sfa / (c1.width + 1))
             | cmp -> cmp *)
      (* Other old attempts: *)
      (* Int.compare (c1.width / c1.steps) (c2.width / c2.steps) *)
      (* Int.compare c1.steps c2.steps *)
      (* match Int.compare c1.width c2.width with *)
      (* | 0 -> Int.compare c1.steps c2.steps *)
      (* | cmp -> cmp *))
    (* (fun c1 c2 -> *)
    (* (\* Dynamic weighing: exploration weight decreases as steps increase *\) *)
    (* let exploration_weight = max 0.1 (1.0 /. (1.0 +. float_of_int (max c1.steps c2.steps))) in *)
    (* let exploitation_weight = 1.0 -. exploration_weight in *)

    (* (\* Measure exploitation by distance from initial width *\) *)
    (* let exploitation1 = float_of_int (init_width - c1.width) in *)
    (* let exploitation2 = float_of_int (init_width - c2.width) in *)

    (* (\* Normalize steps for fair comparison *\) *)
    (* let max_steps = max c1.steps c2.steps in *)
    (* let norm_steps1 = if max_steps = 0 then 0.0 else float_of_int c1.steps /. float_of_int max_steps in *)
    (* let norm_steps2 = if max_steps = 0 then 0.0 else float_of_int c2.steps /. float_of_int max_steps in *)

    (* (\* Weighted score: lower is better (negative exploitation means higher exploitation is better) *\) *)
    (* let score1 = (-.exploitation_weight) *. exploitation1 +. exploration_weight *. norm_steps1 in *)
    (* let score2 = (-.exploitation_weight) *. exploitation2 +. exploration_weight *. norm_steps2 in *)

    (* Float.compare score1 score2) *)
    ()

include Pairing_heap
