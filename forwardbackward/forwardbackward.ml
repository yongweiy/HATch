open Sugar
open Core
open Language
open Rty
open Config
open Option.Let_syntax
open Automatize

exception Incorrectness of RTypectx.ctx * Sft.sft

(** State fingerprint for detecting when forward and backward searches meet *)
type state_fingerprint = {
  eff_depth : int;
  sfa_difficulty : int;
}

let make_fingerprint eff sfa = {
  eff_depth = Rty.depth_of_eff eff;
  sfa_difficulty = Sft.emptiness_check_difficuly_of sfa;
}

let fingerprints_match t1 t2 =
  t1.eff_depth = t2.eff_depth &&
  abs (t1.sfa_difficulty - t2.sfa_difficulty) < 100
  (* Allow some tolerance in difficulty for matching *)

(** Use simple hash tables with fingerprint as key *)
module StateTable = struct
  type t = (state_fingerprint, config) Hashtbl.Poly.t

  let create size = Hashtbl.Poly.create ~size ()

  let find_matching table fingerprint =
    (* Linear search for matching fingerprint *)
    Hashtbl.Poly.fold table ~init:None ~f:(fun ~key ~data acc ->
      match acc with
      | Some _ -> acc
      | None -> if fingerprints_match key fingerprint then Some data else None)

  let add table fingerprint config =
    Hashtbl.Poly.set table ~key:fingerprint ~data:config
end

(** Check if forward and backward searches have met *)
let check_meeting forward_states backward_states config =
  let fingerprint = make_fingerprint config.eff config.sfa in
  match config.dir with
  | Forward ->
      (* Check if backward search has visited a similar state *)
      StateTable.find_matching backward_states fingerprint
  | Backward ->
      (* Check if forward search has visited a similar state *)
      StateTable.find_matching forward_states fingerprint

(** Record a visited state *)
let record_state forward_states backward_states config =
  let fingerprint = make_fingerprint config.eff config.sfa in
  match config.dir with
  | Forward -> StateTable.add forward_states fingerprint config
  | Backward -> StateTable.add backward_states fingerprint config

(** Main bidirectional search algorithm *)
let run opctx rctx eff post pre =
  Printf.printf "\n*** FORWARDBACKWARD.RUN CALLED - delegating to CFG_BIDIRECTIONAL ***\n";
  Out_channel.flush stdout;
  (* Use CFG-based bidirectional search *)
  Cfg_bidirectional.run opctx rctx eff post pre

let run_old opctx rctx eff post pre =
  Printf.printf "\n*** FORWARDBACKWARD.RUN_OLD CALLED ***\n";
  Out_channel.flush stdout;
  (* Initialize worklists for both directions *)
  let init_width_post = Sft.width_of post in
  let init_width_pre = Sft.width_of pre in
  
  let backward_worklist = create_backward_worklist ~init_width:init_width_post in
  let forward_worklist = create_forward_worklist ~init_width:init_width_pre in
  
  (* Initialize backward search from postcondition *)
  add backward_worklist
    (mk_backward rctx eff post init_width_post 0 (Atom Id));

  (* Initialize forward search from precondition *)
  (* Forward search starts with the full effect to consume *)
  add forward_worklist
    (mk_forward rctx eff pre init_width_pre 0 (Atom Id));
  
  (* State tables to track visited states *)
  let forward_states = StateTable.create 1000 in
  let backward_states = StateTable.create 1000 in
  
  let config_counter = ref 0 in
  let forward_counter = ref 0 in
  let backward_counter = ref 0 in
  
  let rec loop () =
    (* Alternate between forward and backward steps *)
    (* Try backward step first *)
    match pop backward_worklist with
    | Some backward_config ->
        incr config_counter;
        incr backward_counter;
        let remaining = Rty.depth_of_eff backward_config.eff in
        Printf.printf
          "[Config #%d] [BACKWARD #%d] width: %d, steps: %d, remaining: %d, difficulty: %d\n"
          !config_counter !backward_counter backward_config.width
          backward_config.steps remaining
          (Sft.emptiness_check_difficuly_of backward_config.sfa);
        Out_channel.flush stdout;

        (* Check if we've met the forward search *)
        (match check_meeting forward_states backward_states backward_config with
        | Some forward_config ->
            Printf.printf
              "*** MEETING POINT FOUND! ***\n\
               Forward steps: %d, Backward steps: %d, Total: %d\n"
              forward_config.steps backward_config.steps
              (forward_config.steps + backward_config.steps);
            Out_channel.flush stdout;

            (* Combine paths from both directions *)
            let combined_path = mk_seq (forward_config.path, backward_config.path) in

            (* Try to find witness from the meeting point *)
            let is_bot = Subtyping.is_bot_cty backward_config.rctx << Cty.mk_unit_from_prop in
            let final_pre = Sft.restrict_domain ~is_bot backward_config.sfa pre in
            let witness_opt, paths_explored = Sft.find_witness ~is_bot final_pre in

            (match witness_opt with
            | Some witness ->
                Printf.printf "Witness found at meeting point!\n";
                Out_channel.flush stdout;
                let pre_regex = Automatize.Regexize.transducer_labels_to_regex witness in
                let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
                let final_eff = mk_seq (admit_pre, combined_path) in
                Some (backward_config.rctx, final_eff)
            | None ->
                Printf.printf "Meeting point found but no witness yet, continuing search...\n";
                Out_channel.flush stdout;
                (* Record state and continue *)
                record_state forward_states backward_states backward_config;
                process_backward_config backward_config;
                loop_forward ())  (* Switch to forward after processing backward *)
        | None ->
            (* No meeting yet, check if we've reached the goal *)
            let is_bot = Subtyping.is_bot_cty backward_config.rctx << Cty.mk_unit_from_prop in
            if Eff.is_identity backward_config.eff then (
              let final_pre = Sft.restrict_domain ~is_bot backward_config.sfa pre in
              (* Sft.print_stats final_pre; *)  (* Disabled to avoid interactive PDF viewer *)
              Out_channel.flush stdout;
              let start_time = Core_unix.gettimeofday () in
              let witness_opt, paths_explored = Sft.find_witness ~is_bot final_pre in
              let end_time = Core_unix.gettimeofday () in
              let elapsed = end_time -. start_time in
              Printf.printf
                "Paths explored in this graph: %d (time: %.3fs, witness: %s)\n"
                paths_explored elapsed
                (if Option.is_some witness_opt then "found" else "not found");
              Out_channel.flush stdout;
              match witness_opt with
              | Some witness ->
                  let pre_regex = Automatize.Regexize.transducer_labels_to_regex witness in
                  let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
                  let combined_eff = mk_seq (admit_pre, backward_config.path) in
                  Some (backward_config.rctx, combined_eff)
              | None ->
                  record_state forward_states backward_states backward_config;
                  loop_forward ()  (* Switch to forward *)
            ) else (
              record_state forward_states backward_states backward_config;
              process_backward_config backward_config;
              loop_forward ()  (* Switch to forward after processing backward *)
            ))
    | None ->
        (* Backward worklist empty, try forward *)
        loop_forward ()

  and loop_forward () =
    (* Process one forward step, then switch to backward *)
    match pop forward_worklist with
    | Some forward_config ->
        incr config_counter;
        incr forward_counter;
        let remaining = Rty.depth_of_eff forward_config.eff in
        Printf.printf
          "[Config #%d] [FORWARD #%d] width: %d, steps: %d, remaining: %d, difficulty: %d\n"
          !config_counter !forward_counter forward_config.width
          forward_config.steps remaining
          (Sft.emptiness_check_difficuly_of forward_config.sfa);
        Out_channel.flush stdout;

        (* Check if we've met the backward search *)
        (match check_meeting forward_states backward_states forward_config with
        | Some backward_config ->
            Printf.printf
              "*** MEETING POINT FOUND! ***\n\
               Forward steps: %d, Backward steps: %d, Total: %d\n"
              forward_config.steps backward_config.steps
              (forward_config.steps + backward_config.steps);
            Out_channel.flush stdout;

            let combined_path = mk_seq (forward_config.path, backward_config.path) in
            let is_bot = Subtyping.is_bot_cty forward_config.rctx << Cty.mk_unit_from_prop in
            let final_pre = Sft.restrict_domain ~is_bot forward_config.sfa pre in
            let witness_opt, paths_explored = Sft.find_witness ~is_bot final_pre in

            (match witness_opt with
            | Some witness ->
                Printf.printf "Witness found at meeting point!\n";
                Out_channel.flush stdout;
                let pre_regex = Automatize.Regexize.transducer_labels_to_regex witness in
                let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
                let final_eff = mk_seq (admit_pre, combined_path) in
                Some (forward_config.rctx, final_eff)
            | None ->
                Printf.printf "Meeting point found but no witness yet, continuing search...\n";
                Out_channel.flush stdout;
                record_state forward_states backward_states forward_config;
                process_forward_config forward_config;
                loop ())  (* Switch back to backward *)
        | None ->
            record_state forward_states backward_states forward_config;
            process_forward_config forward_config;
            loop ())  (* Switch back to backward *)
    | None ->
        (* Both worklists empty - no witness found *)
        None
  
  and process_backward_config config =
    if not @@ Eff.is_identity config.eff then
      Choice.iter
        (Backward_step.step opctx (config.rctx, config.eff, config.sfa, config.path))
        (fun (rctx, eff', sfa, new_path) ->
          let width = Sft.width_of sfa in
          if width < Int.max_value then
            add backward_worklist
              (mk_backward rctx eff' sfa width (config.steps + 1) new_path);
          true)
  
  and process_forward_config config =
    if not @@ Eff.is_identity config.eff then
      Choice.iter
        (Forward_step.step opctx (config.rctx, config.eff, config.sfa, config.path))
        (fun (rctx, eff', sfa, new_path) ->
          let width = Sft.width_of sfa in
          if width < Int.max_value then
            add forward_worklist
              (mk_forward rctx eff' sfa width (config.steps + 1) new_path);
          true)
  in
  
  loop ()

