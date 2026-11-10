open Sugar
open Core
open Language
open Rty
open Eff

(** Backward stepping through effects
    
    This is essentially the same as backwards/step.ml but adapted to work
    within the bidirectional search framework.
*)

(** Backward step: work backwards from postcondition *)
let rec step opctx (rctx, eff, sfa, path) =
  let open Choice in
  let ( let* ) = ( >>= ) in
  let ( let+ ) = Fun.flip map in
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
  
  match eff with
  (* SBAtom: Call operation *)
  | Atom (Trans (Explicit sft)) ->
      (* SBAtom: config{Γ}{SFT}{SFA[post]}{FT} → config{Γ}{ID}{SFA[pre]}{SFT; FT} *)
      let sfa_pre = Sft.mk_compose ~is_bot sft sfa in
      return (rctx, Atom Id, sfa_pre, path)
  
  (* SBChoice: Non-deterministic choice *)
  | Choice (eff1, eff2) ->
      mplus (step opctx (rctx, eff1, sfa, path)) (step opctx (rctx, eff2, sfa, path))
  
  (* SBExist: Existential quantification *)
  | Bind ({ cx; cty }, eff') ->
      let x' = Rename.unique cx in
      let rctx' =
        RTypectx.new_to_right rctx { rx = x'; rty = BaseRty { cty } }
      in
      let eff_subst = subst_eff (cx, AVar x') eff' in
      step opctx (rctx', eff_subst, sfa, path)
  
  (* SBIdent: Identity elimination *)
  | Seq (eff', Atom Id) -> step opctx (rctx, eff', sfa, path)
  | Seq (Guard phi, eff') ->
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' =
        RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } }
      in
      step opctx (rctx', eff', sfa, path)

  (* SBSeq: Sequential composition *)
  | Seq (eff1, eff2) ->
      (* First step eff2, then prepend eff1 to results *)
      let+ rctx', eff2', sfa', path' = step opctx (rctx, eff2, sfa, path) in
      (rctx', Seq (eff1, eff2'), sfa', path')
  
  (* SBGuard: Assumption/Guard *)
  | Guard phi -> 
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' =
        RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } }
      in
      return (rctx', Atom Id, sfa, path)

  (* Base cases *)
  | Atom Id -> return (rctx, Atom Id, sfa, path)
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
      (* Prepend the original Call operation to the path before resolution *)
      let original_call = Atom (Call { op; args; ret = ret_lit }) in
      let new_path = mk_seq (original_call, path) in
      step opctx (rctx, eff', sfa, new_path)
  
  | Constrain (eff1, eff2) ->
      (* Handle Constrain by processing the post-condition (second effect) *)
      step opctx (rctx, eff2, sfa, path)
  
  | Atom (Trans (Admit _ | Append _ | Reject _)) ->
      (* Terminal automata operations *)
      return (rctx, Atom Id, sfa, path)

