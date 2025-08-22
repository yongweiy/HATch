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
    match
      let%bind () = Option.some_if (Eff.is_identity eff) () in
      let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
      let final_pre = Sft.restrict_domain ~is_bot sfa pre in
      let%map witness, _ = Sft.find_witness ~is_bot final_pre in
      (* Create admit_pre from regex representation *)
      let pre_regex = Automatize.Regexize.sft_to_regex final_pre in
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
