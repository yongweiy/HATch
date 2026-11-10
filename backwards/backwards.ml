open Sugar
open Core
open Language
open Rty
open Config
open Step
open Forward_step
open Option.Let_syntax
open Automatize

exception Incorrectness of RTypectx.ctx * Sft.sft

let run opctx rctx eff post pre =
  let init_width = Sft.width_of post in
  let worklist = create_worklist ~init_width in
  add worklist
    { rctx; eff; sfa = post; steps = 0; width = init_width; path = Atom Id };
  let config_counter = ref 0 in
  let rec loop () =
    let%bind { rctx; eff; sfa; steps; width; path } = pop worklist in
    incr config_counter;
    let remaining = Rty.depth_of_eff eff in
    Printf.printf
      "[Config #%d] width: %d, steps: %d, remaining: %d, difficulty: %d\n"
      !config_counter width steps remaining
      (Sft.emptiness_check_difficuly_of sfa);
    (* Sft.print_stats sfa; *)
    Out_channel.flush stdout;
    let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
    match
      let%bind () = Option.some_if (Eff.is_identity eff) () in
      (* print_endline @@ layout_sft sfa; *)
      let final_pre = Sft.restrict_domain ~is_bot sfa pre in
      (* print_endline @@ RTypectx.layout_typed_l @@ List.drop rctx 10; *)
      (* print_endline @@ layout_sft final_pre; *)
      Sft.print_stats final_pre;
      Out_channel.flush stdout;
      let start_time = Core_unix.gettimeofday () in
      let witness_opt, paths_explored =
        Sft.find_witness ~is_bot final_pre
        (* let time, res = clock @@ fun () -> Sft.find_witness ~is_bot final_pre in *)
        (* Printf.printf "%f\n" time; *)
        (* res *)
      in
      let end_time = Core_unix.gettimeofday () in
      let elapsed = end_time -. start_time in
      Printf.printf
        "Paths explored in this graph: %d (time: %.3fs, witness: %s)\n"
        paths_explored elapsed
        (if Option.is_some witness_opt then "found" else "not found");
      Out_channel.flush stdout;
      let%map witness = witness_opt in
      (* print_endline @@ layout_sft final_pre; *)
      (* Create admit_pre from regex representation *)
      let pre_regex =
        (* Automatize.Regexize.sft_to_regex final_pre *)
        Automatize.Regexize.transducer_labels_to_regex witness
      in
      let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
      (* Sequence the presumption with the execution path *)
      let combined_eff = mk_seq (admit_pre, path) in
      (rctx, combined_eff)
    with
    | Some res -> Some res
    | None ->
        if not @@ Eff.is_identity eff then (
          Choice.iter
            ((* let time, res = *)
             (* clock @@ fun () -> *)
             step opctx
               (rctx, eff, sfa, path)
               (* in *)
               (* Printf.printf "%f\n" time; *)
               (* res *))
          @@ fun (rctx, eff', sfa, new_path) ->
          (* Sft.print_stats sfa; *)
          (* Out_channel.flush stdout; *)
          (* print_endline @@ RTypectx.layout_typed_l @@ List.drop rctx 10; *)
          (* print_endline @@ layout_sft sfa; *)
          (* if *)
          (* assert (Option.is_some @@ Sft.find_witness ~is_bot sfa); *)
          (*   (\* if not @@ Subtyping.is_bot_cty rctx @@ Cty.mk_unit_from_prop mk_true *\) *)
          (* then *)
          let width = Sft.width_of sfa in
          if width < Int.max_value then
            add worklist
              {
                rctx;
                eff = eff';
                sfa;
                steps = steps + 1;
                width;
                path = new_path;
              };
          true);
        loop ()
  in
  loop ()

(** Forward-then-backward strategy:
    1. Take N forward steps from entry with precondition
    2. Check if any reached the postcondition
    3. If not, run backward search from each advanced state *)
let run_with_forward_steps opctx rctx eff post pre forward_steps =
  Printf.printf "\n*** FORWARD-BACKWARD: Taking %d forward steps first ***\n" forward_steps;
  Out_channel.flush stdout;

  (* Take N forward steps *)
  let advanced_states = take_n_forward_steps opctx rctx eff pre forward_steps in
  Printf.printf "After %d forward steps: %d reachable states\n"
    forward_steps (List.length advanced_states);
  Out_channel.flush stdout;

  (* Check if any state already satisfies the postcondition *)
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
  let check_state (rctx, eff, sfa, path) =
    if Eff.is_identity eff then
      (* Check if sfa intersects with post *)
      let final_pre = Sft.restrict_domain ~is_bot sfa post in
      let witness_opt, _ = Sft.find_witness ~is_bot final_pre in
      match witness_opt with
      | Some witness ->
          Printf.printf "Found witness during forward exploration!\n";
          Out_channel.flush stdout;
          let pre_regex = Automatize.Regexize.transducer_labels_to_regex witness in
          let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
          let combined_eff = mk_seq (admit_pre, path) in
          Some (rctx, combined_eff)
      | None -> None
    else None
  in

  (* Try to find witness in forward-reached states *)
  match List.find_map advanced_states ~f:check_state with
  | Some result ->
      Printf.printf "Witness found in forward exploration!\n";
      Out_channel.flush stdout;
      Some result
  | None ->
      Printf.printf "No witness in forward states, starting backward search from %d states\n"
        (List.length advanced_states);
      Out_channel.flush stdout;

      (* Run backward search from each advanced state *)
      let run_backward_from_state (rctx_adv, eff_adv, sfa_adv, path_fwd) =
        Printf.printf "\n*** Starting backward search from advanced state ***\n";
        Printf.printf "  Remaining effect depth: %d\n" (Rty.depth_of_eff eff_adv);
        Printf.printf "  SFA width: %d\n" (Sft.width_of sfa_adv);
        Out_channel.flush stdout;

        (* Run standard backward search from this advanced state *)
        let init_width = Sft.width_of post in
        let worklist = create_worklist ~init_width in
        add worklist
          { rctx = rctx_adv; eff = eff_adv; sfa = post; steps = 0; width = init_width; path = Atom Id };
        let config_counter = ref 0 in
        let rec loop () =
          let%bind { rctx; eff; sfa; steps; width; path } = pop worklist in
          incr config_counter;
          let remaining = Rty.depth_of_eff eff in
          if !config_counter mod 100 = 0 then (
            Printf.printf
              "[Backward #%d] width: %d, steps: %d, remaining: %d\n"
              !config_counter width steps remaining;
            Out_channel.flush stdout
          );
          let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
          match
            let%bind () = Option.some_if (Eff.is_identity eff) () in
            (* Check if we can connect to the advanced forward state *)
            let final_pre = Sft.restrict_domain ~is_bot sfa sfa_adv in
            Sft.print_stats final_pre;
            Out_channel.flush stdout;
            let start_time = Core_unix.gettimeofday () in
            let witness_opt, paths_explored = Sft.find_witness ~is_bot final_pre in
            let end_time = Core_unix.gettimeofday () in
            let elapsed = end_time -. start_time in
            Printf.printf
              "Paths explored: %d (time: %.3fs, witness: %s)\n"
              paths_explored elapsed
              (if Option.is_some witness_opt then "found" else "not found");
            Out_channel.flush stdout;
            let%map witness = witness_opt in
            let pre_regex = Automatize.Regexize.transducer_labels_to_regex witness in
            let admit_pre = Eff.Atom (Trans (Admit pre_regex)) in
            (* Combine: forward path + admit + backward path *)
            let combined_eff = mk_seq (mk_seq (path_fwd, admit_pre), path) in
            (rctx, combined_eff)
          with
          | Some res -> Some res
          | None ->
              if not @@ Eff.is_identity eff then (
                Choice.iter
                  (step opctx (rctx, eff, sfa, path))
                @@ fun (rctx, eff', sfa, new_path) ->
                let width = Sft.width_of sfa in
                if width < Int.max_value then
                  add worklist
                    {
                      rctx;
                      eff = eff';
                      sfa;
                      steps = steps + 1;
                      width;
                      path = new_path;
                    };
                true);
              loop ()
        in
        loop ()
      in

      (* Try backward search from each advanced state until one succeeds *)
      List.find_map advanced_states ~f:run_backward_from_state
