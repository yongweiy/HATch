open Sugar
open Core
open Language
open Rty
open Config
open Step
open Option.Let_syntax
open Automatize

exception Incorrectness of RTypectx.ctx * Sft.sft

let run opctx rctx eff post pre =
  let init_width = Sft.width_of post in
  let worklist = create_worklist ~init_width in
  add worklist
    { rctx; eff; sfa = post; steps = 0; width = init_width; path = Atom Id };
  let rec loop () =
    let%bind { rctx; eff; sfa; steps; width; path } = pop worklist in
    let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
    match
      let%bind () = Option.some_if (Eff.is_identity eff) () in
      (* print_endline @@ layout_sft sfa; *)
      let final_pre = Sft.restrict_domain ~is_bot sfa pre in
      (* print_endline @@ RTypectx.layout_typed_l @@ List.drop rctx 10; *)
      (* print_endline @@ layout_sft final_pre; *)
      let%map witness, _ =
        Sft.find_witness ~is_bot final_pre
        (* let time, res = clock @@ fun () -> Sft.find_witness ~is_bot final_pre in *)
        (* Printf.printf "%f\n" time; *)
        (* res *)
      in
      Sft.print_stats final_pre;
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
          Choice.iter (step opctx (rctx, eff, sfa, path))
          @@ fun (rctx, eff', sfa, new_path) ->
          (* Sft.print_stats sfa; *)
          (* Out_channel.flush stdout; *)
          (* print_endline @@ RTypectx.layout_typed_l @@ List.drop rctx 10; *)
          (* print_endline @@ layout_sft sfa; *)
          (* if *)
          (* assert (Option.is_some @@ Sft.find_witness ~is_bot sfa); *)
          (*   (\* if not @@ Subtyping.is_bot_cty rctx @@ Cty.mk_unit_from_prop mk_true *\) *)
          (* then *)
          add worklist
            {
              rctx;
              eff = eff';
              sfa;
              steps = steps + 1;
              width = Sft.width_of sfa;
              path = new_path;
            };
          true);
        loop ()
  in
  loop ()
