open Sugar
open Language
open Rty

(** Convert Constrain queries to Htriple format for srlexec *)

(* All Htriple cases of a (possibly multi-case, i.e. [| ... |]) spec. *)
let rec extract_htriples_from_rty = function
  | ArrRty { rethty; _ } -> extract_htriples_from_hty rethty
  | _ -> []

and extract_htriples_from_hty = function
  | Htriple htriple -> [ htriple ]
  | Rty rty -> extract_htriples_from_rty rty
  | Inter (hty1, hty2) ->
      extract_htriples_from_hty hty1 @ extract_htriples_from_hty hty2
  | _ -> []

(* Ghost parameters (name, type) of an operator type, outermost first *)
let collect_ghost_params hty =
  let rec aux acc hty =
    match hty with
    | Rty (ArrRty { arr = GhostArr Nt.{ x; ty }; rethty }) ->
        aux ((x, ty) :: acc) rethty
    | Rty (ArrRty { arr = _; rethty }) -> aux acc rethty
    | _ -> List.rev acc
  in
  aux [] hty

(* Normal parameters, ghost parameters and Htriple cases of [op]'s spec,
   provided [args] supplies exactly one actual per normal parameter. *)
let extract_op_params_and_htriples oprctx op args =
  match ROpTypectx.get_ty_opt oprctx (Op.EffOp op) with
  | None -> None
  | Some op_rty -> (
      let ghost_params = collect_ghost_params (Rty op_rty) in
      let rec aux acc_rxs hty remaining_args =
        match (hty, remaining_args) with
        | Rty (ArrRty { arr = NormalArr rx; rethty }), _ :: remaining_args' ->
            aux (rx :: acc_rxs) rethty remaining_args'
        | Rty (ArrRty { arr = NormalArr _; _ }), [] -> None
        | Rty (ArrRty { arr = GhostArr _; rethty }), _ ->
            aux acc_rxs rethty remaining_args
        | Rty (ArrRty _), _ -> None
        | _, [] -> Some (List.rev acc_rxs, hty)
        | _, _ :: _ -> None
      in
      match aux [] (Rty op_rty) args with
      | None -> None
      | Some (rxs, hty) -> (
          match extract_htriples_from_hty hty with
          | [] -> None
          | cases -> Some (rxs, ghost_params, cases)))

(* Extract ghost variable from resrty if it has pattern "v == ghost_var" *)
let extract_ghost_var_from_resrty resrty =
  match resrty with
  | BaseRty { cty } ->
      (* Look for equality pattern "v == ghost_var" in phi *)
      let rec find_eq_var phi =
        match phi with
        | Lit (AAppOp (op, [ { x = AVar v; _ }; { x = AVar ghost_var; _ } ]))
          when Op.id_eq_op op.x && String.equal v cty.v.x ->
            Some ghost_var
        | Lit (AAppOp (op, [ { x = AVar ghost_var; _ }; { x = AVar v; _ } ]))
          when Op.id_eq_op op.x && String.equal v cty.v.x ->
            Some ghost_var
        | And props -> List.find_map find_eq_var props
        | _ -> None
      in
      find_eq_var cty.phi
  | _ -> None

(* Translate one query event [Op(args..., ret)] into the HATch precondition SFA
   it denotes: the [pre] of [Op]'s lib_rty_old.ml spec instantiated with the
   actual arguments and observed result.  Returns the SFA together with the
   spec ghosts left free in it; the caller binds those at the top level of the
   query (they are existentially chosen by the witness).

   - Multi-case specs: only the cases whose result refinement admits [ret] are
     kept (e.g. [MemContact (name, false)] selects the [not v] case), and their
     preconditions are joined with [LorA].
   - Capture: spec formals and ghosts are first renamed apart, so an actual
     argument that happens to share a name with a spec variable (e.g.
     [GetNext (a, b)] vs. getNext's ghost [a]) is not substituted again. *)
let call_to_sfa_opt oprctx (ev : Sft.ev) =
  MetaConfig.show_debug_hatch (fun () ->
      Pp.printf "@{<cyan>call_to_sfa_opt@}: op=%s, args=[%s], ret=%s\n" ev.op
        (List.map (fun arg -> layout_lit arg.x) ev.args |> String.concat ", ")
        (layout_lit ev.ret.x));
  match extract_op_params_and_htriples oprctx ev.op ev.args with
  | None ->
      MetaConfig.show_debug_hatch (fun () ->
          Pp.printf "@{<cyan>  extraction failed@}\n");
      None
  | Some (rxs, ghost_params, cases) -> (
      let renaming =
        List.map (fun rx -> (rx.rx, Rename.unique rx.rx)) rxs
        @ List.map (fun (g, _) -> (g, Rename.unique g)) ghost_params
      in
      let fresh x = List.assoc x renaming in
      let rename_sfa sfa =
        List.fold_left (fun acc (x, x') -> subst (x, AVar x') acc) sfa renaming
      in
      let rename_prop phi =
        List.fold_left
          (fun acc (x, x') -> subst_prop (x, AVar x') acc)
          phi renaming
      in
      let arg_substs =
        List.map2 (fun rx arg -> (fresh rx.rx, arg.x)) rxs ev.args
      in
      let instantiate_case { pre; resrty; _ } =
        let substs =
          arg_substs
          @
          match extract_ghost_var_from_resrty resrty with
          | Some g -> [ (fresh g, ev.ret.x) ]
          | None -> []
        in
        let consistent =
          match resrty with
          | BaseRty { cty = { v; phi } } -> (
              let phi =
                List.fold_left
                  (fun acc (x, l) -> subst_prop (x, l) acc)
                  (rename_prop phi) substs
              in
              let phi = subst_prop (v.x, ev.ret.x) phi in
              try Smt.check_sat_bool phi
              with e ->
                Printf.eprintf
                  "[WARNING] constrain_to_htriple: cannot decide whether a %s \
                   case admits ret=%s (%s); keeping it\n\
                   %!"
                  ev.op (layout_lit ev.ret.x) (Printexc.to_string e);
                true)
          | _ -> true
        in
        if consistent then
          Some
            (List.fold_left
               (fun acc (x, l) -> subst (x, l) acc)
               (rename_sfa pre) substs)
        else None
      in
      match List.filter_map instantiate_case cases with
      | [] ->
          MetaConfig.show_debug_hatch (fun () ->
              Pp.printf "@{<cyan>  no case admits ret=%s@}\n"
                (layout_lit ev.ret.x));
          None
      | sfa :: sfas ->
          let sfa = List.fold_left (fun acc s -> LorA (acc, s)) sfa sfas in
          let free = SRL.fv sfa in
          let ghost_binds =
            List.filter_map
              (fun (g, ty) ->
                let g' = fresh g in
                if List.mem g' free then
                  Some { cx = g'; cty = { v = Nt.{ x = v_name; ty }; phi = mk_true } }
                else None)
              ghost_params
          in
          MetaConfig.show_debug_hatch (fun () ->
              Pp.printf "@{<cyan>  %i/%i case(s) admit ret; pre@}: %s\n"
                (List.length sfas + 1) (List.length cases) (layout_regex sfa));
          Some (sfa, ghost_binds))

(* Extract SFA from effect body (after all Binds), plus the spec ghosts it
   leaves free.  Sequential events are conjoined over the same final history
   ([LandA]); this is faithful only for non-consuming observations (reads),
   not for events whose new-format spec [Reject]s, e.g. dequeuing. *)
let rec extract_sfa_from_body oprctx eff =
  match eff with
  | Eff.Atom (Call ev) -> call_to_sfa_opt oprctx ev
  | Eff.Seq (eff1, eff2) -> (
      match
        (extract_sfa_from_body oprctx eff1, extract_sfa_from_body oprctx eff2)
      with
      | Some (sfa1, binds1), Some (sfa2, binds2) ->
          Some (LandA (sfa1, sfa2), binds1 @ binds2)
      | _ -> None)
  | Eff.Atom (Trans (Explicit sft_id)) when Syntax.Rty.Sft.(sft_id = mk_ident)
    ->
      Some (mk_allA, [])
  | _ -> None

(* Extract ghost bindings and the inner Constrain *)
let rec extract_binds_and_constrain eff =
  match eff with
  | Eff.Bind (cx, eff') ->
      let binds, constrain_opt = extract_binds_and_constrain eff' in
      (cx :: binds, constrain_opt)
  | Eff.Constrain (eff1, eff2) -> ([], Some (eff1, eff2))
  | _ -> ([], None)

(* Convert Monad with Constrain to Htriple, returning (cxs, hty) *)
(* param_substs: substitutions to apply for parameters (e.g., elm -> elm_ghost) *)
let rec convert_hty param_substs oprctx hty =
  match hty with
  | Monad { ret; eff } -> (
      let binds, constrain_opt = extract_binds_and_constrain eff in
      match constrain_opt with
      | Some (eff1, eff2) -> (
          (* Apply parameter substitutions to effects first *)
          let eff1_param_subst =
            List.fold_left
              (fun eff_acc (old_var, new_var) ->
                subst_eff_id (old_var, new_var) eff_acc)
              eff1 param_substs
          in

          let eff2_param_subst =
            List.fold_left
              (fun eff_acc (old_var, new_var) ->
                subst_eff_id (old_var, new_var) eff_acc)
              eff2 param_substs
          in

          (* Check if ret appears free in the effect *)
          let eff_combined = Eff.Seq (eff1_param_subst, eff2_param_subst) in
          let ret_is_free = List.mem ret.rx (fv_eff eff_combined) in
          let new_binds, resrty, eff1_subst, eff2_subst =
            if ret_is_free then
              (* Introduce a ghost variable for ret *)
              let ghost_var = ret.rx ^ "_ghost" in
              let ret_cty = rty_force_cty ret.rty in
              let ghost_cx = { cx = ghost_var; cty = ret_cty } in
              (* Update ret.rty to include equality constraint with ghost variable *)
              let updated_rty =
                match ret.rty with
                | BaseRty { cty } ->
                    let eq_lit =
                      mk_lit_eq_lit cty.v.ty (AVar cty.v.x) (AVar ghost_var)
                    in
                    let eq_prop = Lit eq_lit in
                    let new_phi = mk_and cty.phi eq_prop in
                    BaseRty { cty = { cty with phi = new_phi } }
                | _ -> ret.rty
              in
              (* Substitute ret -> ret_ghost in effects *)
              let eff1_subst =
                subst_eff_id (ret.rx, ghost_var) eff1_param_subst
              in
              let eff2_subst =
                subst_eff_id (ret.rx, ghost_var) eff2_param_subst
              in
              (binds @ [ ghost_cx ], updated_rty, eff1_subst, eff2_subst)
            else (binds, ret.rty, eff1_param_subst, eff2_param_subst)
          in

          (* Apply parameter substitutions to ghost bindings *)
          let new_binds_subst =
            List.map
              (fun cx ->
                let cty_subst =
                  List.fold_left
                    (fun cty_acc (old_var, new_var) ->
                      Cty.subst_id (old_var, new_var) cty_acc)
                    cx.cty param_substs
                in
                { cx with cty = cty_subst })
              new_binds
          in

          match
            ( extract_sfa_from_body oprctx eff1_subst,
              extract_sfa_from_body oprctx eff2_subst )
          with
          | Some (sfa_pre, ghosts_pre), Some (sfa_post, ghosts_post) ->
              let htriple =
                Htriple { pre = sfa_pre; resrty; post = ComplementA sfa_post }
              in
              (new_binds_subst @ ghosts_pre @ ghosts_post, htriple)
          | _ ->
              (* Leaving the Monad in place would make srlexec run zero
                 triples and print a bare "type check failed". *)
              failwith
                "constrain_to_htriple: cannot translate query: some event's op \
                 has no Htriple-format spec in lib_rty_old.ml, no case of it \
                 admits the observed result, or the effect is not a sequence \
                 of calls (rerun with the \"hatch\" debug tag for details)")
      | None -> ([], hty))
  | Inter (h1, h2) ->
      let binds1, hty1 = convert_hty param_substs oprctx h1 in
      let binds2, hty2 = convert_hty param_substs oprctx h2 in
      (binds1 @ binds2, Inter (hty1, hty2))
  | Rty rty ->
      let binds, rty' = convert_rty param_substs oprctx rty in
      (binds, Rty rty')
  | _ -> ([], hty)

and convert_rty param_substs oprctx = function
  | BaseRty _ as rty -> ([], rty)
  | ArrRty { arr; rethty } ->
      (* First pass: convert return type to collect ghost bindings *)
      let binds, rethty' = convert_hty param_substs oprctx rethty in

      (* Check if any ghost bindings reference this parameter *)
      let param_name_opt, param_rty_opt =
        match arr with
        | NormalArr { rx; rty } -> (Some rx, Some rty)
        | GhostArr Nt.{ x; _ } ->
            (Some x, None) (* Ghost params don't need ghosts *)
        | ArrArr _ -> (None, None)
      in

      let param_is_referenced =
        match param_name_opt with
        | None -> false
        | Some param_name ->
            List.exists (fun cx -> List.mem param_name (Cty.fv cx.cty)) binds
      in

      (* If parameter is referenced, create ghost version and re-process *)
      if param_is_referenced then
        match (param_name_opt, param_rty_opt) with
        | Some rx, Some rty ->
            let ghost_var = rx ^ "_ghost" in
            (* Create ghost binding for param_ghost with same type as parameter *)
            let param_ghost_cx = { cx = ghost_var; cty = rty_force_cty rty } in

            (* Add equality constraint param == param_ghost to parameter's type *)
            let updated_rty =
              match rty with
              | BaseRty { cty } ->
                  let eq_lit =
                    mk_lit_eq_lit cty.v.ty (AVar cty.v.x) (AVar ghost_var)
                  in
                  let eq_prop = Lit eq_lit in
                  let new_phi = mk_and cty.phi eq_prop in
                  BaseRty { cty = { cty with phi = new_phi } }
              | _ -> rty
            in

            (* Re-process return type with substitution rx -> ghost_var *)
            let new_param_substs = (rx, ghost_var) :: param_substs in
            let binds_final, rethty_final =
              convert_hty new_param_substs oprctx rethty
            in

            (* Return with param_ghost at the front *)
            let all_binds = param_ghost_cx :: binds_final in
            ( all_binds,
              ArrRty
                {
                  arr = NormalArr { rx; rty = updated_rty };
                  rethty = rethty_final;
                } )
        | _ ->
            (* Shouldn't happen but handle gracefully *)
            ( binds,
              ArrRty
                { arr = convert_arr param_substs oprctx arr; rethty = rethty' }
            )
      else
        ( binds,
          ArrRty { arr = convert_arr param_substs oprctx arr; rethty = rethty' }
        )

and convert_arr param_substs oprctx = function
  | NormalArr { rx; rty } ->
      let binds, rty' = convert_rty param_substs oprctx rty in
      if not (List.is_empty binds) then
        Printf.printf
          "[WARNING] Ghost bindings found in normal argument, should be at top \
           level\n\
           %!";
      NormalArr { rx; rty = rty' }
  | GhostArr _ as arr -> arr
  | ArrArr rty ->
      let binds, rty' = convert_rty param_substs oprctx rty in
      if not (List.is_empty binds) then
        Printf.printf
          "[WARNING] Ghost bindings found in arrow argument, should be at top \
           level\n\
           %!";
      ArrArr rty'

(* Convert a single structure entry, collecting ghost bindings *)
let convert_structure_entry_with_binds oprctx entry =
  match entry with
  | Structure.Rty { name; kind; rty } ->
      let binds, rty' = convert_rty [] oprctx rty in
      (binds, Structure.Rty { name; kind; rty = rty' })
  | _ -> ([], entry)

(* Convert assertions in structure, collecting all ghost bindings *)
let convert_structure oprctx structure =
  let entries_with_binds =
    List.map (convert_structure_entry_with_binds oprctx) structure
  in
  let all_binds = List.concat_map fst entries_with_binds in
  let new_structure = List.map snd entries_with_binds in
  (all_binds, new_structure)
