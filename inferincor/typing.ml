open Sugar
open Language
open Rty

let refine_to_ceil : Nt.t -> rty = function
  | Ty_arrow _ -> _failatwith __FILE__ __LINE__ "TODO: refine_to_ceil"
  | ty -> mk_rty_var_sat_prop "_" #: ty mk_true

let under_to_over : rty -> rty = Fun.id

let of_ty_pre ty pre =
  { ret = "ret" #:: (refine_to_ceil ty); eff = Eff.Guard pre }

let of_rty rty = { ret = "ret" #:: rty; eff = Eff.Atom Eff.Id }
let under_to_over_rtyped { rx; rty } = { rx; rty = under_to_over rty }

let existential { rx = cx; rty } =
  match rty with
  | ArrRty _ -> Fun.id
  | BaseRty { cty } -> (
      function[@warning "-8"]
      | { ret; eff } ->
          assert (not @@ List.exists (String.equal cx) @@ fv_rty ret.rty);
          { ret; eff = Eff.Bind ((cx #::: cty), eff) })

let multi_existential rxs = List.fold_right existential rxs

(** Union* and Inter* rules implementation *)

(* InterOver and UnionOver rules for base types *)
let inter_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  assert (v1 = v2);
  { v = v1; phi = mk_and phi1 phi2 }

let union_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  assert (v1 = v2);
  { v = v1; phi = mk_or phi1 phi2 }

(* InterUnder and UnionUnder rules *)
let inter_rty = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      BaseRty { cty = union_cty cty1 cty2 }  (* InterUnder: phi1 ∨ phi2 *)
  | _ -> _failatwith __FILE__ __LINE__ "inter_rty"

let union_rty = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      BaseRty { cty = inter_cty cty1 cty2 }  (* UnionUnder: phi1 ∧ phi2 *)
  | _ -> _failatwith __FILE__ __LINE__ "union_rty"

let union_effty rctx monad1 monad2 =
  let ret_rty = union_rty (monad1.ret.rty, monad2.ret.rty) in
  let ret = { rx = monad1.ret.rx; rty = ret_rty } in
  let eff = Eff.Choice (monad1.eff, monad2.eff) in
  { ret; eff }

(* InterEff rule *)
let inter_effty rctx tau1 tau2 =
  let t = union_rty (tau1.ret.rty, tau2.ret.rty) in
  let ret = { rx = tau1.ret.rx; rty = t } in
  let eff = Eff.Choice (tau1.eff, tau2.eff) in
  { ret; eff }

(** WK* rules implementation - Top-level type weakening *)

(* WKPure rule: Γ ⊢ v ↑ t, Γ ⊢ t₁ ∨ t = t₂ ⟹ Γ ⊢ t₁ ↓ v ↑ t₂ *)
let weaken_pure_type rctx t1 t =
  let t2 = union_rty (t1, t) in
  t2

(* WKEff rule: Γ ⊢ e ↑ τ, Γ ⊢ τ₁ ∨ τ = τ₂ ⟹ Γ ⊢ τ₁ ↓ e ↑ τ₂ *)  
let weaken_eff_type rctx tau1 tau =
  let tau2 = union_effty rctx tau1 tau in
  tau2

(** Phase 2: Type weakening entry point *)
let weaken_with_query rctx (inferred_type : rty) (query_type : rty) : rty option =
  try
    let result = weaken_pure_type rctx query_type inferred_type in
    if Subtyping.is_bot_rty rctx result then None
    else Some result
  with
  | _ -> None

let weaken_eff_with_query rctx (inferred_eff : monad) (query_eff : monad) : monad option =
  try
    let result = weaken_eff_type rctx query_eff inferred_eff in
    if Subtyping.is_bot_rty rctx result.ret.rty then None
    else Some result
  with
  | _ -> None

