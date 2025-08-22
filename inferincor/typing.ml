open Zzdatatype.Zlist
open Sugar
open Core.Option.Let_syntax
open Language
open Rty

(** Type union and intersection operations following Union* and Inter* rules *)

(** Helper functions for type construction *)
let mk_ceil_pure : Nt.t -> rty = function
  | Ty_arrow _ -> _failatwith __FILE__ __LINE__ "TODO: mk_ceil_pure"
  | ty -> mk_rty_var_sat_prop "_" #: ty mk_true

let mk_ceil_eff ty =
  let rty = mk_ceil_pure ty in
  {
    ret = "ret" #:: rty;
    eff =
      Eff.Constrain
        ( Atom (Trans (Explicit Sft.mk_ident)),
          Atom (Trans (Explicit Sft.mk_ident)) );
  }

let under_to_over : rty -> rty = Fun.id
let of_rty rty = { ret = "ret" #:: rty; eff = Eff.Atom Eff.Id }
let under_to_over_rtyped { rx; rty } = { rx; rty = under_to_over rty }

let skolemize cty =
  match (cty.v.ty, cty.phi) with
  | Ty_unit, phi when is_true phi -> Some (AC Const.U)
  | Ty_bool, Iff (Lit (AVar v), Lit lit) when String.equal cty.v.x v -> Some lit
  | _, Lit (AAppOp (op, [ a; b ]))
    when Op.id_eq_op op.x && equal_lit a.x (AVar cty.v.x) ->
      Some b.x
  | _ -> None

(** Existential quantification *)
let existential_eff { rx = cx; rty } =
  match rty with
  | ArrRty _ -> Fun.id
  | BaseRty { cty } -> (
      fun eff ->
        match skolemize cty with
        | Some lit -> subst_eff (cx, lit) eff
        | None -> mk_bind cx #::: cty eff)

let multi_existential_eff rxs = List.fold_right existential_eff rxs

let existential rx { ret; eff } =
  match ret.rty with
  | BaseRty { cty } when not @@ List.mem rx.rx @@ Cty.fv cty ->
      { ret; eff = existential_eff rx eff }
  | BaseRty _ | ArrRty _ -> _failatwith __FILE__ __LINE__ "unimp"

let multi_existential = List.fold_right existential

let externalize = function
  | { rx; rty = ArrRty _ } -> Fun.id
  | { rx; rty = BaseRty { cty } } -> (
      fun monad ->
        match (skolemize cty, monad.ret.rty) with
        | Some lit_of_rx, _ -> subst_monad (rx, lit_of_rx) monad
        | None, BaseRty { cty } when List.mem rx @@ Cty.fv cty ->
            {
              ret = { monad.ret with rty = mk_top cty.v.ty };
              eff =
                mk_seq
                  ( Guard (subst_prop_id (cty.v.x, monad.ret.rx) cty.phi),
                    monad.eff );
            }
        | None, BaseRty _ -> monad
        | None, ArrRty _ -> _failatwith __FILE__ __LINE__ "die")

let multi_externalize = List.fold_right externalize

(** Union* and Inter* rules implementation *)
let eff_bind monadx (x, eff) : Eff.t =
  match monadx.ret.rty with
  | ArrRty _ -> mk_seq (monadx.eff, eff)
  | BaseRty { cty } -> (
      match skolemize cty with
      | Some lit_of_rx ->
          mk_seq
            ( subst_eff (monadx.ret.rx, lit_of_rx) monadx.eff,
              subst_eff (x, lit_of_rx) eff )
      | None ->
          let x' = Rename.unique x in
          mk_bind x' #::: cty
          @@ mk_seq
               ( subst_eff_id (monadx.ret.rx, x') monadx.eff,
                 subst_eff_id (x, x') eff ))

(* InterOver and UnionOver rules for base types *)
let inter_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  assert (v1 = v2);
  return { v = v1; phi = mk_and phi1 phi2 }

let union_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  assert (v1 = v2);
  return { v = v1; phi = mk_or phi1 phi2 }

(* InterUnder and UnionUnder rules *)
let rec inter_rty opctx = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      let%map cty = union_cty cty1 cty2 in
      BaseRty { cty }
      (* InterUnder: phi1 ∨ phi2 *)
  | ( ArrRty { arr = arr1; rethty = rethty1 },
      ArrRty { arr = arr2; rethty = rethty2 } ) ->
      (* InterArr rule: contravariant in argument, covariant in return *)
      let%bind arr = inter_arr opctx arr1 arr2 in
      let%map rethty = inter_hty opctx rethty1 rethty2 in
      ArrRty { arr; rethty }
  | _ -> _failatwith __FILE__ __LINE__ "inter_rty"

and inter_arr opctx arr1 arr2 =
  match (arr1, arr2) with
  | NormalArr rx1, NormalArr rx2 ->
      assert (rx1.rx = rx2.rx);
      let%map rty = union_rty opctx (rx1.rty, rx2.rty) in
      NormalArr { rx = rx1.rx; rty }
  | _ -> _failatwith __FILE__ __LINE__ "inter_arr"

and inter_hty opctx hty1 hty2 =
  match (hty1, hty2) with
  | Monad m1, Monad m2 ->
      let%map m = inter_effty opctx [] m1 m2 in
      Monad m
  | Rty r1, Rty r2 ->
      let%map r = inter_rty opctx (r1, r2) in
      Rty r
  | _ -> _failatwith __FILE__ __LINE__ "inter_hty"

and union_rty opctx = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      let%map cty = inter_cty cty1 cty2 in
      BaseRty { cty }
      (* UnionUnder: phi1 ∧ phi2 *)
  | ( ArrRty { arr = arr1; rethty = rethty1 },
      ArrRty { arr = arr2; rethty = rethty2 } ) ->
      (* UnionArr rule: contravariant in argument, covariant in return *)
      let%bind arr = union_arr opctx arr1 arr2 in
      let%map rethty = union_hty opctx rethty1 rethty2 in
      ArrRty { arr; rethty }
  | _ -> _failatwith __FILE__ __LINE__ "union_rty"

and union_arr opctx arr1 arr2 =
  match (arr1, arr2) with
  | NormalArr rx1, NormalArr rx2 ->
      assert (rx1.rx = rx2.rx || rx1.rx = "_" || rx2.rx = "_");
      let%map rty = inter_rty opctx (rx1.rty, rx2.rty) in
      NormalArr { rx = rx1.rx; rty }
  | _ -> _failatwith __FILE__ __LINE__ "union_arr"

and union_hty opctx hty1 hty2 =
  match (hty1, hty2) with
  | Monad m1, Monad m2 ->
      let%map m = union_effty opctx [] m1 m2 in
      Monad m
  | Rty r1, Rty r2 ->
      let%map r = union_rty opctx (r1, r2) in
      Rty r
  | _ ->
      _failatwith __FILE__ __LINE__
        (spf "union_hty fail:\n%s\n%s\n" (layout_hty hty1) (layout_hty hty2))

(* UnionEff and InterEff rules *)
and union_effty opctx rctx monad1 monad2 =
  let rec get_constrain_info rxs = function
    | Eff.Bind (cx, eff) ->
        let rxs = (cx.cx #:: (BaseRty { cty = cx.cty })) :: rxs in
        get_constrain_info rxs eff
    | Eff.Constrain (Atom (Trans (Explicit sft1)), Atom (Trans (Explicit sft2)))
      ->
        (List.rev rxs, Sft.mk_ran sft1, Sft.mk_ran sft2)
    | eff ->
        Printf.printf "Unhandled constrain pattern: %s\n" @@ layout_eff eff;
        _failatwith __FILE__ __LINE__ "die"
  in
  let%bind ret_rty = union_rty opctx (monad1.ret.rty, monad2.ret.rty) in
  let ret = { rx = monad1.ret.rx; rty = ret_rty } in
  let rxs, pre, post = get_constrain_info [] monad1.eff in
  (* [rctx'] includes a variable denoting return value and ghost variables
     within query *)
  let rctx' = RTypectx.new_to_rights (RTypectx.new_to_right rctx ret) rxs in
  print_endline @@ layout_hty (Monad monad2);
  (* [rctx''] further includes intermediate variables along the
     execution path explored *)
  let%bind rctx'', combined_eff =
    Backwards.run opctx rctx' monad2.eff post pre
  in
  (* [rxs] includes ghost variables and intermediate variables *)
  let rxs = RTypectx.to_rxs @@ List.drop (List.length rctx + 1) rctx'' in
  (* Apply existential quantification to the entire witness effect *)
  let witness_eff = multi_existential_eff rxs combined_eff in
  (* Return the properly constructed monad *)
  return { ret; eff = witness_eff }

and inter_effty opctx rctx tau1 tau2 =
  let%map t = union_rty opctx (tau1.ret.rty, tau2.ret.rty) in
  let ret = { rx = tau1.ret.rx; rty = t } in
  let eff = Eff.Choice (tau1.eff, tau2.eff) in
  { ret; eff }
