open Language
module RCtx = RTypectx
module ROpCtx = ROpTypectx
module R = Rty
open Nt
open Sugar

let pprint_res_one (id, name, res, timef) =
  match res with
  | Some _ ->
      Printf.printf
        "Task %i(%s): exec time %f(s), incorrectness inference succeeded\n" id
        name timef
  | None ->
      Printf.printf
        "Task %i(%s): exec time %f(s), incorrectness inference failed\n" id name
        timef

let infer ?(unroll_bound = 1) (opctx', rctx') structure normalized =
  let opctx, rctx = ROpCtx.from_code structure in
  let opctx = opctx' @ opctx in
  let rctx = rctx' @ rctx in
  let tasks = RCtx.get_task structure in
  List.mapi
    (fun id (name, rty) ->
      let id = id + 1 in
      let () =
        MetaConfig.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>Task %i:@}\n" id
      in
      match
        List.find_opt (fun (name', _) -> String.equal name name') normalized
      with
      | None -> failwith "cannot find the implemetation of the given assertion"
      | Some (_, comp) ->
          let comp = TypedCoreEff.to_v comp in
          (* print_endline @@ Denormalize.layout_value comp; *)
          let () =
            if not (Nt.eq comp.ty (R.erase_rty rty)) then
              let () =
                Printf.printf
                  "The erased type of the refinement type mismacted the \
                   implementation:\n\
                   %s (rty) !=\n\
                   %s (imp)\n"
                  (Nt.layout (R.erase_rty rty))
                  (Nt.layout comp.ty)
              in
              _failatwith __FILE__ __LINE__ "input error"
            else ()
          in

          (* let () = Printf.printf "%s\n" @@ R.layout_rty rty in *)
          (* let () = failwith "end" in *)
          (* let () = do_stat comp rty in *)
          (* let () = Smt.stat_init () in *)
          (* let () = Baux.stat_init () in *)
          (* let () = Desymbolic.stat_init () in *)
          (* let _ = Rty.Ax.get_related_assumption [] in *)

          (* Process input rty to replace Call effects with actual operator effects *)
          let processed_rty = Rty_processor.process_input_rty opctx rty in
          (* Apply automatize to convert sequences to automata *)
          let automatized_rty = Automatize.do_rty rctx processed_rty in
          (* Printf.printf "user query:\n%s\n" @@ Rty.layout_rty automatized_rty; *)
          let typecheck_time, res =
            Sugar.clock (fun () ->
                (* Interleaved weakening and inference *)
                (* try *)
                Weaken.weaken_pure ~unroll_bound opctx rctx automatized_rty comp
                (* with *)
                (* | _ -> *)
                (* print_endline "failed"; *)
                (* None *))
          in
          (* let stat = *)
          (*   Stat.update_dynamic_stat stat typecheck_time *)
          (*     (Smt.stat_get_cur ()) (Baux.stat_get_cur ()) *)
          (*     (Desymbolic.stat_get_cur ()) *)
          (* in *)
          (* let if_type_checked = *)
          (*   match res with Some () -> true | None -> false *)
          (* in *)
          (* let () = *)
          (*   MetaConfig.show_debug_typing @@ fun _ -> *)
          (*   pprint_res_one (id, name, res, typecheck_time) *)
          (* in *)
          (* let () = Stat.settTypeCheck (if_type_checked, typecheck_time) in *)
          (* let elrond_stat_record = Infer_ghost.get_stat () in *)
          (* let () = *)
          (*   Printf.printf "len: %i\n" (List.length elrond_stat_record); *)
          (*   failwith "end" *)
          (* in *)
          (* let stat = Stat.update_elrond stat elrond_stat_record in *)
          (id, name, res, typecheck_time))
    tasks

(** Bidirectional search version of infer *)
let infer_bidirectional ?(unroll_bound = 1) (opctx', rctx') structure normalized =
  let opctx, rctx = ROpCtx.from_code structure in
  let opctx = opctx' @ opctx in
  let rctx = rctx' @ rctx in
  let tasks = RCtx.get_task structure in
  List.mapi
    (fun id (name, rty) ->
      let id = id + 1 in
      let () =
        MetaConfig.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>Task %i (BIDIRECTIONAL):@}\n" id
      in
      match
        List.find_opt (fun (name', _) -> String.equal name name') normalized
      with
      | None -> failwith "cannot find the implemetation of the given assertion"
      | Some (_, comp) ->
          let comp = TypedCoreEff.to_v comp in
          let () =
            if not (Nt.eq comp.ty (R.erase_rty rty)) then
              let () =
                Printf.printf
                  "The erased type of the refinement type mismacted the \
                   implementation:\n\
                   %s (rty) !=\n\
                   %s (imp)\n"
                  (Nt.layout (R.erase_rty rty))
                  (Nt.layout comp.ty)
              in
              _failatwith __FILE__ __LINE__ "input error"
            else ()
          in

          (* Process input rty to replace Call effects with actual operator effects *)
          Printf.printf "*** INFER_BIDIRECTIONAL: calling process_input_rty ***\n";
          Out_channel.flush stdout;
          let processed_rty = Rty_processor.process_input_rty opctx rty in
          Printf.printf "*** INFER_BIDIRECTIONAL: calling Automatize.do_rty ***\n";
          Out_channel.flush stdout;
          (* Apply automatize to convert sequences to automata *)
          let automatized_rty = Automatize.do_rty rctx processed_rty in
          Printf.printf "*** INFER_BIDIRECTIONAL: calling weaken_pure_bidirectional ***\n";
          Out_channel.flush stdout;
          let typecheck_time, res =
            Sugar.clock (fun () ->
                (* Use bidirectional weakening instead of regular weakening *)
                Weaken.weaken_pure_bidirectional ~unroll_bound opctx rctx automatized_rty comp)
          in
          (id, name, res, typecheck_time))
    tasks

let infer_forward_backward ~unroll_bound ~forward_steps (opctx', rctx') structure normalized =
  let opctx, rctx = ROpCtx.from_code structure in
  let opctx = opctx' @ opctx in
  let rctx = rctx' @ rctx in
  let tasks = RCtx.get_task structure in
  List.mapi
    (fun id (name, rty) ->
      let id = id + 1 in
      let () =
        MetaConfig.show_debug_typing @@ fun _ ->
        Pp.printf "@{<bold>Task %i (FORWARD-BACKWARD):@}\n" id
      in
      match
        List.find_opt (fun (name', _) -> String.equal name name') normalized
      with
      | None -> failwith "cannot find the implemetation of the given assertion"
      | Some (_, comp) ->
          let comp = TypedCoreEff.to_v comp in
          let () =
            if not (Nt.eq comp.ty (R.erase_rty rty)) then
              let () =
                Printf.printf
                  "The erased type of the refinement type mismacted the \
                   implementation:\n\
                   %s (rty) !=\n\
                   %s (imp)\n"
                  (Nt.layout (R.erase_rty rty))
                  (Nt.layout comp.ty)
              in
              _failatwith __FILE__ __LINE__ "input error"
            else ()
          in

          (* Process input rty to replace Call effects with actual operator effects *)
          Printf.printf "*** INFER_FORWARD_BACKWARD: calling process_input_rty ***\n";
          Out_channel.flush stdout;
          let processed_rty = Rty_processor.process_input_rty opctx rty in
          Printf.printf "*** INFER_FORWARD_BACKWARD: calling Automatize.do_rty ***\n";
          Out_channel.flush stdout;
          (* Apply automatize to convert sequences to automata *)
          let automatized_rty = Automatize.do_rty rctx processed_rty in
          Printf.printf "*** INFER_FORWARD_BACKWARD: calling weaken_pure_forward_backward ***\n";
          Out_channel.flush stdout;
          let typecheck_time, res =
            Sugar.clock (fun () ->
                (* Use forward-backward weakening *)
                Weaken.weaken_pure_forward_backward ~unroll_bound ~forward_steps opctx rctx automatized_rty comp)
          in
          (id, name, res, typecheck_time))
    tasks
