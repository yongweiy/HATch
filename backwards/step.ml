open Sugar
open Language
open Rty
open Eff

(** stepping between triples *)
let rec step (rctx, eff, sfa) = 
  match eff with
  (* SBAtom: Call operation *)
  | Atom (Trans (Explicit sft)) ->
      (* Compose Γ, SFT, SFA_post to get SFA_pre *)
      let sfa_pre = (* TODO: implement Compose function *) sfa in
      [(rctx, Atom Id, sfa_pre)]
  
  (* SBChoice: Non-deterministic choice *)
  | Choice (eff1, eff2) ->
      [(rctx, eff1, sfa); (rctx, eff2, sfa)]
  
  (* SBExist: Existential quantification *)
  | Bind ({ cx; cty }, eff') ->
      (* Generate fresh variable name *)
      let x' = Rename.unique cx in
      (* Extend context: Γ' = Γ, x' : τ *)
      let rctx' = RTypectx.new_to_right rctx { rx = x'; rty = BaseRty { cty } } in
      (* Substitute x with x' in eff' *)
      let eff_subst = subst_eff (cx, AVar x') eff' in
      [(rctx', eff_subst, sfa)]
  
  (* SBSeq: Sequential composition *)
  | Seq (eff1, eff2) ->
      (* First step eff2, then prepend eff1 to results *)
      let successors = step (rctx, eff2, sfa) in
      List.map (fun (rctx', eff2', sfa') -> 
        (rctx', Seq (eff1, eff2'), sfa')) successors
  
  (* SBIdent: Identity elimination *)
  | Seq (eff', Atom Id) ->
      [(rctx, eff', sfa)]
  
  (* SBGuard: Assumption/Guard *)
  | Guard phi ->
      (* Generate fresh variable for unit type with constraint φ *)
      let u = Rename.unique "u" in
      let unit_cty = Cty.mk_unit_from_prop phi in
      let rctx' = RTypectx.new_to_right rctx { rx = u; rty = BaseRty { cty = unit_cty } } in
      [(rctx', Atom Id, sfa)]
  
  (* SBUntilZero and SBUntilStep would require Until construct *)
  (* These seem to be missing from the current Eff.t definition *)
  
  (* Base cases *)
  | Atom Id -> 
      (* Identity - no further steps *)
      []
  
  | Atom (Call _) ->
      (* Function calls - would need more context about how to handle *)
      []
  
  | Atom (Trans _) ->
      (* Other transitions - would need specific handling *)
      []
  
  | Reach eff' ->
      (* Reachability - step the inner effect *)
      step (rctx, eff', sfa)
