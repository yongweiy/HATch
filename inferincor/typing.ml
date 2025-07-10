open Sugar
open Language
open Rty

(** Type union and intersection operations following Union* and Inter* rules *)

(** Helper functions for type construction *)
let mk_ceil_pure : Nt.t -> rty = function
  | Ty_arrow _ -> _failatwith __FILE__ __LINE__ "TODO: mk_ceil_pure"
  | ty -> mk_rty_var_sat_prop "_" #: ty mk_true

let mk_ceil_eff ty =
  let rty = mk_ceil_pure ty in
  { ret = "ret" #:: rty; eff = Eff.Reach (Atom (Trans (Explicit (Sft.mk_ident)))) }

let under_to_over : rty -> rty = Fun.id
let of_rty rty = { ret = "ret" #:: rty; eff = Eff.Atom Eff.Id }
let under_to_over_rtyped { rx; rty } = { rx; rty = under_to_over rty }

(** Existential quantification *)
let existential { rx = cx; rty } =
  match rty with
  | ArrRty _ -> Fun.id
  | BaseRty { cty } ->
      fun { ret; eff } ->
        assert (not @@ List.exists (String.equal cx) @@ fv_rty ret.rty);
        { ret; eff = Eff.Bind (cx #::: cty, eff) }

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
      BaseRty { cty = union_cty cty1 cty2 } (* InterUnder: phi1 ∨ phi2 *)
  | ArrRty { arr = arr1; rethty = rethty1 }, ArrRty { arr = arr2; rethty = rethty2 } ->
      (* InterArr rule: contravariant in argument, covariant in return *)
      let arr = inter_arr arr1 arr2 in
      let rethty = inter_hty rethty1 rethty2 in
      ArrRty { arr; rethty }
  | _ -> _failatwith __FILE__ __LINE__ "inter_rty"

and inter_arr arr1 arr2 =
  match arr1, arr2 with
  | NormalArr rx1, NormalArr rx2 ->
      assert (rx1.rx = rx2.rx);
      NormalArr { rx = rx1.rx; rty = union_rty (rx1.rty, rx2.rty) }
  | _ -> _failatwith __FILE__ __LINE__ "inter_arr"

and inter_hty hty1 hty2 =
  match hty1, hty2 with
  | Monad m1, Monad m2 -> Monad (inter_effty [] m1 m2)
  | Rty r1, Rty r2 -> Rty (inter_rty (r1, r2))
  | _ -> _failatwith __FILE__ __LINE__ "inter_hty"

let union_rty = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      BaseRty { cty = inter_cty cty1 cty2 } (* UnionUnder: phi1 ∧ phi2 *)
  | ArrRty { arr = arr1; rethty = rethty1 }, ArrRty { arr = arr2; rethty = rethty2 } ->
      (* UnionArr rule: contravariant in argument, covariant in return *)
      let arr = union_arr arr1 arr2 in
      let rethty = union_hty rethty1 rethty2 in
      ArrRty { arr; rethty }
  | _ -> _failatwith __FILE__ __LINE__ "union_rty"

and union_arr arr1 arr2 =
  match arr1, arr2 with
  | NormalArr rx1, NormalArr rx2 ->
      assert (rx1.rx = rx2.rx);
      NormalArr { rx = rx1.rx; rty = inter_rty (rx1.rty, rx2.rty) }
  | _ -> _failatwith __FILE__ __LINE__ "union_arr"

and union_hty hty1 hty2 =
  match hty1, hty2 with
  | Monad m1, Monad m2 -> Monad (union_effty [] m1 m2)
  | Rty r1, Rty r2 -> Rty (union_rty (r1, r2))
  | _ -> _failatwith __FILE__ __LINE__ "union_hty"

(* UnionEff and InterEff rules *)
and union_effty rctx monad1 monad2 =
  let ret_rty = union_rty (monad1.ret.rty, monad2.ret.rty) in
  let ret = { rx = monad1.ret.rx; rty = ret_rty } in
  let eff = Eff.Choice (monad1.eff, monad2.eff) in
  { ret; eff }

and inter_effty rctx tau1 tau2 =
  let t = union_rty (tau1.ret.rty, tau2.ret.rty) in
  let ret = { rx = tau1.ret.rx; rty = t } in
  let eff = Eff.Choice (tau1.eff, tau2.eff) in
  { ret; eff }
