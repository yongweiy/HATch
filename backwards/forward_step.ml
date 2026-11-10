open Sugar
open Core
open Language
open Rty
open Eff

(** Forward stepping: advance from entry point with precondition SFA
    Returns (rctx, remaining_eff, sfa, path_taken) *)
let rec forward_step opctx (rctx, eff, sfa, path) =
  let open Choice in
  let ( let* ) = ( >>= ) in
  let ( let+ ) = Fun.flip map in
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
  
  match eff with
  (* FwdAtom: Process transducer in forward direction *)
  | Atom (Trans (Explicit sft)) ->
      (* Forward: compose SFA with SFT to get output SFA *)
      let sfa_post = Sft.mk_compose ~is_bot sfa sft in
      return (rctx, Atom Id, sfa_post, path)
  
  (* FwdChoice: Non-deterministic choice - explore both branches *)
  | Choice (eff1, eff2) ->
      mplus 
        (forward_step opctx (rctx, eff1, sfa, path)) 
        (forward_step opctx (rctx, eff2, sfa, path))
  
  (* FwdBind: Existential quantification *)
  | Bind ({ cx; cty }, eff') ->
      let x' = Rename.unique cx in
      let rctx' = RTypectx.new_to_right rctx { rx = x'; rty = BaseRty { cty } } in
      let eff_subst = subst_eff (cx, AVar x') eff' in
      forward_step opctx (rctx', eff_subst, sfa, path)
  
  (* FwdSeq: Sequential composition - process first effect first *)
  | Seq (Atom Id, eff2) -> 
      forward_step opctx (rctx, eff2, sfa, path)
  
  | Seq (Guard phi, eff') ->
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' = RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } } in
      forward_step opctx (rctx', eff', sfa, path)
  
  | Seq (eff1, eff2) ->
      (* Process eff1 first, then continue with eff2 *)
      let+ rctx', eff1', sfa', path' = forward_step opctx (rctx, eff1, sfa, path) in
      (rctx', Seq (eff1', eff2), sfa', path')
  
  (* FwdGuard: Process guard *)
  | Guard phi ->
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' = RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } } in
      return (rctx', Atom Id, sfa, path)
  
  (* FwdCall: Resolve call to its effect *)
  | Atom (Call { op; args; ret = ret_lit }) ->
      let op_rty = Rty (ROpTypectx.get_ty opctx (EffOp op)) in
      let rec extract_params_and_rethty ?(param_substs = []) current_hty remaining_args =
        match remaining_args with
        | [] -> (param_substs, current_hty)
        | arg_lit :: rest_args -> (
            let rty = hty_force_rty current_hty in
            let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
            match arr with
            | ArrArr _ | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
            | NormalArr rx ->
                extract_params_and_rethty
                  ~param_substs:((rx.rx, arg_lit.x) :: param_substs)
                  rethty rest_args)
      in
      let param_substs, rethty = extract_params_and_rethty op_rty args in
      let { ret; eff } = hty_force_monad rethty in
      let eff' =
        Core.List.fold_right
          ((ret.rx, ret_lit.x) :: param_substs)
          ~init:eff ~f:subst_eff
      in
      (* Add the call to the path *)
      let original_call = Atom (Call { op; args; ret = ret_lit }) in
      let new_path = mk_seq (path, original_call) in
      forward_step opctx (rctx, eff', sfa, new_path)
  
  (* FwdConstrain: Process pre-condition (first effect) *)
  | Constrain (eff1, eff2) ->
      forward_step opctx (rctx, eff1, sfa, path)
  
  (* Base cases *)
  | Atom Id -> return (rctx, Atom Id, sfa, path)
  | Atom (Trans (Admit _ | Append _ | Reject _)) ->
      return (rctx, Atom Id, sfa, path)

(** Take N forward steps from entry point
    Returns list of all reachable states after N steps *)
let take_n_forward_steps opctx rctx eff pre n =
  let rec loop states remaining_steps =
    if remaining_steps = 0 then states
    else
      (* Take one step from each state *)
      let new_states = 
        List.concat_map states ~f:(fun (rctx, eff, sfa, path) ->
          if Eff.is_identity eff then
            (* Already at identity, can't step further *)
            [(rctx, eff, sfa, path)]
          else
            (* Take one forward step *)
            Choice.to_list (forward_step opctx (rctx, eff, sfa, path))
        )
      in
      loop new_states (remaining_steps - 1)
  in
  loop [(rctx, eff, pre, Atom Id)] n

