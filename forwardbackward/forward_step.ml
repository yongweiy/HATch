open Sugar
open Core
open Language
open Rty
open Eff

(** Forward stepping through effects
    
    This is the dual of backwards/step.ml - instead of working backwards from
    postcondition to precondition, we work forwards from precondition.
    
    Forward stepping consumes the effect from left to right and propagates
    the automaton forward through compositions.
*)

(** Forward step: consume effect and propagate automaton forward *)
let rec step opctx (rctx, eff, sfa, path) =
  Printf.printf "*** FORWARD_STEP.STEP called with eff: %s ***\n" (Rty.layout_eff eff);
  Out_channel.flush stdout;
  let open Choice in
  let ( let* ) = ( >>= ) in
  let ( let+ ) = Fun.flip map in
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in

  match eff with
  (* FAtom: Explicit transducer - compose forward *)
  | Atom (Trans (Explicit sft)) ->
      (* Forward: config{Γ}{SFT; eff'}{SFA[pre]} → config{Γ}{eff'}{SFA ∘ SFT} *)
      let sfa_post = Sft.mk_compose ~is_bot sfa sft in
      return (rctx, Atom Id, sfa_post, path)
  
  (* FChoice: Non-deterministic choice - explore both branches *)
  | Choice (eff1, eff2) ->
      mplus (step opctx (rctx, eff1, sfa, path)) (step opctx (rctx, eff2, sfa, path))
  
  (* FBind: Existential quantification *)
  | Bind ({ cx; cty }, eff') ->
      let x' = Rename.unique cx in
      let rctx' =
        RTypectx.new_to_right rctx { rx = x'; rty = BaseRty { cty } }
      in
      let eff_subst = subst_eff (cx, AVar x') eff' in
      step opctx (rctx', eff_subst, sfa, path)
  
  (* FSeq: Sequential composition - process left to right *)
  | Seq (eff1, eff2) ->
      (* Forward: first process eff1, then continue with eff2 *)
      let* rctx', eff1', sfa', path' = step opctx (rctx, eff1, sfa, path) in
      if Eff.is_identity eff1' then
        (* eff1 fully consumed, continue with eff2 *)
        step opctx (rctx', eff2, sfa', path')
      else
        (* eff1 not fully consumed, keep it in sequence *)
        return (rctx', Seq (eff1', eff2), sfa', path')
  
  (* FGuard: Process guard constraint *)
  | Guard phi ->
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' =
        RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } }
      in
      return (rctx', Atom Id, sfa, path)
  
  (* FIdent: Identity - nothing to do *)
  | Atom Id -> return (rctx, Atom Id, sfa, path)
  
  (* FCall: Resolve call to its effect specification *)
  | Atom (Call { op; args; ret = ret_lit }) ->
      let op_rty = Rty (ROpTypectx.get_ty opctx (EffOp op)) in
      let rec extract_params_and_rethty ?(param_substs = []) current_hty
          remaining_args =
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
      (* Append the original Call operation to the path *)
      let original_call = Atom (Call { op; args; ret = ret_lit }) in
      let new_path = mk_seq (path, original_call) in
      step opctx (rctx, eff', sfa, new_path)
  
  (* FConstrain: Process the pre-condition (first effect) *)
  | Constrain (eff1, eff2) ->
      step opctx (rctx, eff1, sfa, path)
  
  (* Terminal automata operations *)
  | Atom (Trans (Admit _ | Append _ | Reject _)) ->
      return (rctx, Atom Id, sfa, path)

