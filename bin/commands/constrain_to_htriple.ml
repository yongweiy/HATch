open Sugar
open Language
open Rty

(** Convert Constrain queries to Htriple format for srlexec *)

(* Extract htriple from rty by traversing arrow types *)
let rec extract_htriple_from_rty = function
  | ArrRty { rethty = Htriple htriple; _ } -> Some htriple
  | ArrRty { rethty = Rty rty; _ } -> extract_htriple_from_rty rty
  | _ -> None

(* Helper to extract htriple from hty *)
let rec extract_htriple_from_hty = function
  | Htriple htriple -> Some htriple
  | Rty rty -> extract_htriple_from_rty rty
  | Inter (hty1, hty2) -> (
      (* TODO: as a implementation shortcut, we under-approximate extract either branch of the intersection *)
      match extract_htriple_from_hty hty1 with
      | Some _ as result -> result
      | None -> extract_htriple_from_hty hty2)
  | _ -> None

(* Helper to collect ghost parameters from hty *)
let collect_ghost_params hty =
  let rec aux acc hty =
    match hty with
    | Rty (ArrRty { arr = GhostArr Nt.{ x; _ }; rethty }) ->
        aux (x :: acc) rethty
    | Rty (ArrRty { arr = _; rethty }) ->
        aux acc rethty
    | _ -> List.rev acc
  in
  aux [] hty

(* Helper to extract parameters and htriple from operator type *)
let extract_op_params_and_htriple oprctx op args =
  match ROpTypectx.get_ty_opt oprctx (Op.EffOp op) with
  | Some op_rty ->
      (* First collect ghost parameters from the full type *)
      let ghost_params = collect_ghost_params (Rty op_rty) in

      let rec extract_params_and_htriple acc_rxs hty remaining_args =
        match hty with
        | Rty (ArrRty { arr; rethty }) -> (
            match arr with
            | NormalArr rx -> (
                match remaining_args with
                | [] ->
                    (* No more arguments but still have normal params - error *)
                    None
                | arg :: remaining_args' ->
                    extract_params_and_htriple (rx :: acc_rxs) rethty
                      remaining_args')
            | GhostArr _ ->
                (* Skip ghost parameters - don't consume from remaining_args *)
                extract_params_and_htriple acc_rxs rethty remaining_args
            | _ -> None)
        | _ -> (
            (* No more parameters, extract the htriple *)
            match remaining_args with
            | [] -> (
                match extract_htriple_from_hty hty with
                | Some htriple -> Some (List.rev acc_rxs, ghost_params, htriple)
                | None -> None)
            | _ ->
                (* Still have arguments but no more parameters - error *)
                None)
      in
      extract_params_and_htriple [] (Rty op_rty) args
  | None -> None

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

(* Extract SFA from operation Call by looking up its library spec and applying arguments *)
let call_to_sfa_opt oprctx (ev : Sft.ev) =
  MetaConfig.show_debug_hatch (fun () ->
      Pp.printf "@{<cyan>call_to_sfa_opt@}: op=%s, args=[%s], ret=%s\n"
        ev.op
        (List.map (fun arg -> layout_lit arg.x) ev.args |> String.concat ", ")
        (layout_lit ev.ret.x));
  match extract_op_params_and_htriple oprctx ev.op ev.args with
  | Some (rxs, ghost_params, { pre; resrty; post }) ->
      MetaConfig.show_debug_hatch (fun () ->
          Pp.printf "@{<cyan>  extracted htriple@}: params=[%s], ghosts=[%s]\n"
            (List.map (fun rx -> rx.rx) rxs |> String.concat ", ")
            (String.concat ", " ghost_params));

      (* Find which ghost parameter equals the return value *)
      let ret_ghost_var_opt = extract_ghost_var_from_resrty resrty in
      MetaConfig.show_debug_hatch (fun () ->
          Pp.printf "@{<cyan>  ret_ghost_var@}: %s\n"
            (match ret_ghost_var_opt with Some v -> v | None -> "none"));

      (* Create substitutions for formal parameters to actual arguments *)
      let param_substitutions =
        List.map2 (fun rx arg -> (rx.rx, arg.x)) rxs ev.args
      in

      (* Create substitutions for ghost parameters *)
      let ghost_substitutions =
        List.map
          (fun ghost_var ->
            match ret_ghost_var_opt with
            | Some ret_ghost when String.equal ghost_var ret_ghost ->
                (* This ghost equals the return value, substitute with ev.ret *)
                (ghost_var, ev.ret.x)
            | _ ->
                (* This ghost doesn't equal the return value, rename it uniquely *)
                let unique_name = Rename.unique ghost_var in
                (ghost_var, AVar unique_name))
          ghost_params
      in

      let all_substitutions = param_substitutions @ ghost_substitutions in

      MetaConfig.show_debug_hatch (fun () ->
          Pp.printf "@{<cyan>  all_substitutions@}: [%s]\n"
            (List.map (fun (var, lit) -> Printf.sprintf "%s -> %s" var (layout_lit lit)) all_substitutions
             |> String.concat ", "));

      (* Apply substitutions to the precondition SFA *)
      let pre_subst =
        List.fold_left
          (fun sfa_acc (var, lit_val) -> subst (var, lit_val) sfa_acc)
          pre all_substitutions
      in
      Some pre_subst
  | None ->
      MetaConfig.show_debug_hatch (fun () ->
          Pp.printf "@{<cyan>  extraction failed@}\n");
      (* If extraction failed, it might be an operation that doesn't need SFA tracking *)
      (* For now, return None - the caller should handle this *)
      None

(* Extract SFA from effect body (after all Binds) *)
let rec extract_sfa_from_body oprctx eff =
  match eff with
  | Eff.Atom (Call ev) -> call_to_sfa_opt oprctx ev
  | Eff.Seq (eff1, eff2) -> (
      match
        (extract_sfa_from_body oprctx eff1, extract_sfa_from_body oprctx eff2)
      with
      | Some sfa1, Some sfa2 -> Some (LandA (sfa1, sfa2))
      | _ -> None)
  | Eff.Atom (Trans (Explicit sft_id)) when Syntax.Rty.Sft.(sft_id = mk_ident)
    ->
      Some mk_allA
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
                      mk_lit_eq_lit cty.v.ty (AVar ret.rx) (AVar ghost_var)
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
          | Some sfa_pre, Some sfa_post ->
              let htriple =
                Htriple { pre = sfa_pre; resrty; post = ComplementA sfa_post }
              in
              (new_binds_subst, htriple)
          | _ -> ([], hty))
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
                    mk_lit_eq_lit cty.v.ty (AVar rx) (AVar ghost_var)
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
