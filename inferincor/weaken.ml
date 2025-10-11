open Sugar
open Core.Option.Let_syntax
open Language
open TypedCoreEff
open Rty
open Typing

(** Interleaved type weakening and inference following updated rules *)

(** Type synthesis for values following Syn* rules *)
let rec infer_pure opctx rctx (value : value typed) : rty =
  match value.x with
  | VConst c ->
      (* SynConst rule: Γ ⊢ c ↑ {b | ν = c} *)
      mk_rty_var_eq_c value.ty c
  | VVar x -> (
      (* SynVar and SynVarFun rules *)
      match RTypectx.get_ty_opt rctx x with
      | Some rty -> (
          match rty with
          | BaseRty _ -> mk_rty_var_eq_var x #: value.ty
          | ArrRty _ -> rty)
      | None -> mk_rty_var_eq_var x #: value.ty)
  | VLam { lamarg; lambody } -> (
      (* SynFun rule modified: takes input type from context *)
      let rx = { rx = lamarg.x; rty = mk_ceil_pure lamarg.ty } in
      let rctx' = RTypectx.new_to_right rctx rx in
      let { ret; eff } = infer_eff opctx rctx' lambody in
      match ret.rty with
      | ArrRty _ when Eff.is_identity eff ->
          ArrRty { arr = NormalArr rx; rethty = Rty ret.rty }
      | _ -> ArrRty { arr = NormalArr rx; rethty = Monad { ret; eff } })
  | VFix { fixname; fixarg; fixbody } ->
      let func = (VLam { lamarg = fixarg; lambody = fixbody }) #: value.ty in
      (* Handle recursive functions with zero-depth inlining for under-approximation:
         Add function to context with bottom return type (no behavior) *)
      let rec make_bottom = function
        | Nt.Ty_arrow (arg_ty, ret_ty) ->
            Rty
              (ArrRty
                 {
                   arr = NormalArr { rx = "_"; rty = mk_ceil_pure arg_ty };
                   rethty = make_bottom ret_ty;
                 })
        | ty ->
            Monad
              {
                ret = { rx = "ret"; rty = Rty.mk_bot ty };
                eff = Eff.Atom Eff.Id;
              }
      in
      let rec unroll ?(fuel = 1) fix_type =
        if fuel < 0 then fix_type
        else
          let rctx' =
            RTypectx.new_to_right rctx { rx = fixname.x; rty = fix_type }
          in
          unroll ~fuel:(fuel - 1) @@ infer_pure opctx rctx' func
      in
      unroll @@ hty_force_rty @@ make_bottom value.ty
      (* let fix_type0 = hty_force_rty @@ make_bottom value.ty in *)
      (* let rctx0 = *)
      (*   RTypectx.new_to_right rctx { rx = fixname.x; rty = fix_type0 } *)
      (* in *)
      (* let fix_type1 = infer_pure opctx rctx0 func in *)
      (* let rctx1 = *)
      (*   RTypectx.new_to_right rctx { rx = fixname.x; rty = fix_type1 } *)
      (* in *)
      (* infer_pure opctx rctx1 func *)
  | VTu _ -> _failatwith __FILE__ __LINE__ "die"

(** Type synthesis for computations following Syn* rules *)
and infer_eff opctx rctx (expr : comp typed) : monad =
  match expr.x with
  | CVal v ->
      (* SynLift rule: Γ ⊢ v ↑ t, FT[r] = ret v ⟹ Γ ⊢ v ↑ M(t, FT[r]) *)
      let t = infer_pure opctx rctx v #: expr.ty in
      let ret = { rx = "ret"; rty = t } in
      { ret; eff = Eff.Atom Eff.Id }
  | CLetE { lhs; rhs; letbody } ->
      let locals, monadx =
        match rhs.x with
        | CAppOp { op; appopargs } ->
            let arg_rtys =
              List.map (fun arg -> infer_pure opctx rctx arg) appopargs
            in
            infer_op_application opctx rctx lhs op arg_rtys
        | CApp { appf; apparg } ->
            let appf_rty = infer_pure opctx rctx appf in
            let apparg_rty = infer_pure opctx rctx apparg in
            let func_hty = Rty appf_rty in
            infer_function_application opctx rctx lhs.x [ apparg_rty ] func_hty
        | _ -> ([], infer_eff opctx rctx rhs)
      in
      let rx = { rx = lhs.x; rty = monadx.ret.rty } in
      let rctx' =
        RTypectx.new_to_right (RTypectx.new_to_rights rctx locals) rx
      in
      let monad =
        multi_externalize locals @@ externalize rx
        @@ infer_eff opctx rctx' letbody
      in
      {
        monad with
        eff = multi_existential_eff locals @@ eff_bind monadx (rx.rx, monad.eff);
      }
  | CMatch { matched; match_cases } ->
      (* SynMatch rule: infer type for each case and join them together *)
      (* let matched_rty = infer_pure opctx rctx matched in *)
      let[@warning "-8"] (hd_monad :: tl_monads) =
        List.map
          (fun { constructor; args; exp } ->
            let matched = _value_to_lit __FILE__ __LINE__ matched in
            let phi =
              mk_prop_lit_eq_lit matched.ty matched.x
              @@
              if String.equal constructor.x "True" then AC (Const.B true)
              else if String.equal constructor.x "False" then AC (Const.B false)
              else _failatwith __FILE__ __LINE__ "UNIMP"
            in
            let rx =
              (Rename.unique "br") #:: (Rty.mk_from_prop Ty_unit @@ fun _ -> phi)
            in
            existential rx
            @@ infer_eff opctx (RTypectx.new_to_right rctx rx) exp)
          match_cases
      in
      let[@warning "-8"] aux
          { ret = { rx; rty = BaseRty { cty = { phi; v } } }; eff } =
        {
          ret = { rx; rty = BaseRty { cty = { phi; v } } };
          eff = Seq (Guard (subst_prop_id (v_name, rx) phi), eff);
        }
      in
      List.fold_left
        (fun [@warning "-8"] {
                               ret =
                                 {
                                   rx = rx_acc;
                                   rty = BaseRty { cty = { phi = phi_acc; v } };
                                 };
                               eff = eff_acc;
                             } monad ->
          let[@warning "-8"] {
                           ret = { rx; rty = BaseRty { cty = { phi; _ } } };
                           eff;
                         } =
            aux monad
          in
          assert (String.equal rx_acc rx);
          let rty = mk_from_prop v.ty @@ fun _ -> mk_or phi_acc phi in
          let eff = Eff.Choice (eff_acc, eff) in
          { ret = rx #:: rty; eff })
        (aux hd_monad) tl_monads
  | _ -> _failatwith __FILE__ __LINE__ "die"

(** Type weakening for values following WK* rules *)
and weaken_pure opctx rctx (rty_in : rty) (value : value typed) : rty option =
  match value.x with
  | VLam { lamarg; lambody } -> (
      (* Handle lambda weakening with input type (updated SynFun rule) *)
      let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty_in in
      match arr with
      | ArrArr _ -> _failatwith __FILE__ __LINE__ "Higher order function"
      | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
      | NormalArr rx ->
          (* SynFun rule: Γ,x:t_x ⊢ τ₁ ↓ e ↑ τ₂ ⟹ Γ ⊢ x:t_x→τ₁ ↓ λx.e ↑ x:t_x→τ₂ *)
          assert (rx.rx = lamarg.x);
          let rctx' = RTypectx.new_to_right rctx rx in
          let%map hty = weaken_eff opctx rctx' rethty lambody in
          ArrRty { arr = NormalArr rx; rethty = hty }
          |> tap @@ fun result_rty ->
             assert (not @@ Subtyping.is_bot_rty rctx result_rty))
  | _ ->
      (* WKPure rule: Γ ⊢ v ↑ t, Γ ⊢ t₁ ∨ t = t₂ ⟹ Γ ⊢ t₁ ↓ v ↑ t₂ *)
      let inferred_rty = infer_pure opctx rctx value in
      union_rty opctx rctx rty_in inferred_rty

(** Type weakening for computations following WK* rules *)
and weaken_eff opctx rctx (hty_in : hty) (expr : comp typed) : hty option =
  match hty_in with
  | Monad monad_in ->
      (* WKEff rule: Γ ⊢ e ↑ τ, Γ ⊢ τ₁ ∨ τ = τ₂ ⟹ Γ ⊢ τ₁ ↓ e ↑ τ₂ *)
      let%map monad_out =
        union_effty opctx rctx monad_in @@ infer_eff opctx rctx expr
      in
      Monad monad_out
  | Rty rty_in ->
      let%map rty_out =
        union_rty opctx rctx rty_in @@ infer_pure opctx rctx @@ to_v expr
      in
      Rty rty_out
  | _ -> _failatwith __FILE__ __LINE__ "die"

(** Generic function application logic *)
and infer_function_application opctx rctx lhs_name arg_rtys func_hty :
    string rtyped list * monad =
  let rec multi_app rxs arg_rtys hty =
    match arg_rtys with
    | [] -> (List.rev rxs, hty)
    | arg_rty :: arg_rtys -> (
        let rty = hty_force_rty hty in
        let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
        match arr with
        | ArrArr _ ->
            _failatwith __FILE__ __LINE__ "Higher order function application"
        | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
        | NormalArr rx ->
            let rx' =
              match union_rty opctx rctx rx.rty arg_rty with
              | Some rty -> { rx = rx.rx ^ "_" ^ lhs_name; rty }
              | None ->
                  _failatwith __FILE__ __LINE__
                    "union_rty failed in function application"
            in
            multi_app (rx' :: rxs) arg_rtys
            @@ subst_hty_id (rx.rx, rx'.rx) rethty)
  in
  let rxs, hty = multi_app [] arg_rtys func_hty in
  let monad = hty_to_monad __FILE__ __LINE__ hty in
  (rxs, monad)

(** Operator application inference *)
and infer_op_application opctx rctx lhs (op : Op.t typed) arg_rtys :
    string rtyped list * monad =
  let func_hty = Rty (ROpTypectx.get_ty opctx op.x) in
  let rxs, base_monad =
    infer_function_application opctx rctx lhs.x arg_rtys func_hty
  in
  let monad =
    match op.x with
    | Op.BuiltinOp _ -> base_monad
    | Op.EffOp op_name ->
        (* Create Call effect instead of exposing specific effect *)
        let args =
          List.map (fun rty -> { x = AVar rty.rx; ty = erase_rty rty.rty }) rxs
        in
        let ret =
          { x = AVar base_monad.ret.rx; ty = erase_rty base_monad.ret.rty }
        in
        let call_effect = Eff.Atom (Eff.Call { op = op_name; args; ret }) in
        { base_monad with eff = call_effect }
    | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
  in
  (rxs, monad)
