open Zzdatatype.Datatype
open Language
open TypedCoreEff
open Rty
open Syntax
open Sugar

let ( let* ) x f = Choice.bind f x
let ( let^ ) x f = Choice.fmap f x
let ( let+ ) x f = Choice.map f x
let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

(* TODO: are those still needed? *)

(* equality checking between typed and untyped variables *)

let with_same_op ev1 ev2 = String.equal ev1.op ev2.op
let typed_eq_untyped x y = String.equal x.x y
let untyped_eq_typed x y = String.equal x y.x
let compare_typed x y = String.compare x.x y.x

let typed_eq_typed x y =
  if String.equal x.x y.x then (
    _assert __FILE__ __LINE__
      (spf "%s = %s"
         (layout_typed (fun x -> x) x)
         (layout_typed (fun x -> x) y))
      (x.ty = y.ty);
    true)
  else false

(* collect qualifier *)

let rename ~op ~index arg =
  String.sub op 0 1 ^ "_" ^ Int.to_string index ^ "!" ^ arg

let rename_xs ~rename xs =
  let ys = List.map (fun x -> rename #-> x) xs in
  let substs = List.map2 (fun x y -> (x.x, y.x)) xs ys in
  (ys, substs)

(* TODO: split prop if possible *)
let rxs_of_xs prop xs =
  match List.last_destruct_opt xs with
  | None -> []
  | Some (xs, x) ->
      List.map (fun x -> x.x #:: (mk_rty_var_sat_prop x mk_true)) xs
      @ [ x.x #:: (mk_rty_var_sat_prop x prop) ]

(* qualifier-related *)

let print_query ~rctx ~gvars phi =
  Pp.printf "%s, %s ⊢ %s\n"
    (RTypectx.layout_typed_l rctx)
    (Rty.layout_typed_l Fun.id gvars)
    (layout_prop phi)

let check_prop ~rctx phi =
  (* print_query ~rctx ~gvars phi; *)
  (* let rctx = *)
  (*   RTypectx.new_to_rights rctx *)
  (*   @@ List.map (fun { x; ty } -> { rx = x; rty = Rty.mk_top ty }) gvars *)
  (* in *)
  (* let rctx = *)
  (*   RTypectx.new_to_right rctx *)
  (*     { rx = Rename.unique "a"; rty = Rty.mk_unit_rty_from_prop phi } *)
  (* in *)
  let lhs_rty = Rty.mk_top Nt.unit_ty in
  (* let rhs_rty = Rty.mk_bot Nt.unit_ty in *)
  let rhs_rty = Rty.mk_unit_rty_from_prop phi in
  Subtyping.sub_rty_bool rctx (lhs_rty, rhs_rty)

let forall_ignore_unit us prop =
  let fvs = fv_prop prop in
  List.fold_left
    (fun prop u ->
      if u.ty = Nt.unit_ty || (not @@ StrList.exists u.x fvs) then prop
      else Forall (u, prop))
    prop us

let exists_ignore_unit us prop =
  let fvs = fv_prop prop in
  List.fold_left
    (fun prop u ->
      if u.ty = Nt.unit_ty || (not @@ StrList.exists u.x fvs) then prop
      else Exists (u, prop))
    prop us

(* deriv *)

(* let lit_entails_sev ~rctx ~gvars ~ghosts ~index lit sev = *)
(*   (\* TODO: guard event *\) *)
(*   let ev = *)
(*     match sev with *)
(*     | EffEvent ev -> ev *)
(*     | GuardEvent _ -> *)
(*         _failatwith __FILE__ __LINE__ "lit_entails_sev: GuardEvent" *)
(*   in *)
(*   let entails ({ op = op1; vs = vs1; v = v1; phi = phi1 } : eff_event) *)
(*       ({ op = op2; vs = vs2; v = v2; phi = phi2 } : eff_event) = *)
(*     _assert __FILE__ __LINE__ "sev_entails_sev: op" (op1 = op2); *)
(*     _assert __FILE__ __LINE__ "sev_entails_sev: vs" (vs1 = vs2); *)
(*     _assert __FILE__ __LINE__ "sev_entails_sev: v" (v1 = v2); *)
(*     check_prop ~rctx ~gvars *)
(*     @@ forall_ignore_unit (v1 :: vs1) *)
(*     @@ smart_implies phi1 phi2 *)
(*   in *)
(*   let opt_of_bool elem b = if b then Some elem else None in *)
(*   let res_of_bool b = if b then Some ([], []) else None in *)
(*   match lit with *)
(*   | { events = [ ev' ]; op_filter = `Whitelist [] } when with_same_op ev' ev *)
(*     -> ( *)
(*       let vs = ev.v :: ev.vs in *)
(*       let fvs = List.sort_uniq compare_typed @@ typed_fv_prop ev.phi in *)
(*       let fvs = List.substract typed_eq_typed fvs gvars in *)
(*       match List.intersect_and_subtract typed_eq_typed fvs ghosts with *)
(*       | [], _ -> res_of_bool @@ entails ev' ev *)
(*       | ghosts, locals -> *)
(*           if not @@ entails ev' { ev with phi = mk_true } then *)
(*             (\* TODO: is the simple skolemization an over/under approx *\) *)
(*             None *)
(*           else *)
(*             let locals, substs = *)
(*               rename_xs ~rename:(rename ~op:ev.op ~index) locals *)
(*             in *)
(*             (\* Pp.printf "locals: %s\n" @@ layout_typed_l (fun x -> x) locals; *\) *)
(*             let phi' = P.multisubst_prop_id substs ev'.phi in *)
(*             let phi = P.multisubst_prop_id substs ev.phi in *)
(*             if *)
(*               (not (List.is_empty locals)) *)
(*               && (RTypectx.exists rctx @@ (List.hd locals).x) *)
(*             then *)
(*               (\* ghost state already revealed *\) *)
(*               Some ([], rxs_of_xs phi ghosts) *)
(*             else Some (rxs_of_xs phi' locals, rxs_of_xs phi ghosts)) *)
(*   | { events = []; op_filter = `Whitelist [ op ] } when ev.op = op -> *)
(*       res_of_bool @@ entails { ev with phi = mk_true } ev *)
(*   | { events = []; op_filter = `Blacklist ops } -> res_of_bool false *)
(*   | _ -> res_of_bool false *)

(** separate out events whose qualifier reference to variables in
    `rctx`, and impose constraint from the qualifier
    TODO: is this only necessary when the constraint comes from SFA being checked?
*)
(* let refine ~index (rctx, { events; op_filter }) = *)
(*   let events, refined = *)
(*     List.partition_map *)
(*       (fun ({ op; vs; v; phi } as ev) -> *)
(*         let fvs = List.sort_uniq compare_typed @@ typed_fv_prop phi in *)
(*         let vs, fvs = *)
(*           List.intersect_and_subtract typed_eq_typed fvs (v :: vs) *)
(*         in *)
(*         if not @@ List.exists (fun fv -> RTypectx.exists rctx fv.x) fvs then *)
(*           Left ev *)
(*         else *)
(*           let vs, substs = rename_xs ~rename:(rename ~op ~index) vs in *)
(*           let phi = P.multisubst_prop_id substs phi in *)
(*           let rctx = RTypectx.new_to_rights rctx @@ rxs_of_xs phi vs in *)
(*           Right (rctx, of_sevent @@ EffEvent ev)) *)
(*       (\* let rxs = *\) *)
(*       (\*   List.map *\) *)
(*       (\*     (fun v -> { rx = rename ~op ~index v.x; rty = Rty.mk_top v.ty }) *\) *)
(*       (\*     vs *\) *)
(*       (\* in *\) *)
(*       (\* let rctx = RTypectx.new_to_rights rctx rxs in *\) *)
(*       (\* let phi = *\) *)
(*       (\*   List.fold_left *\) *)
(*       (\*     (fun phi (v, rx) -> subst_prop_id (v.x, rx.rx) phi) *\) *)
(*       (\*     phi *\) *)
(*       (\*   @@ List.combine vs rxs *\) *)
(*       (\* in *\) *)
(*       (\* let rctx = *\) *)
(*       (\*   RTypectx.new_to_right rctx *\) *)
(*       (\*   @@ ((Rename.unique "u") #:: (mk_unit_rty_from_prop phi)) *\) *)
(*       (\* in *\) *)
(*       (\* Pp.printf "rctx:\n%s\n" @@ RTypectx.layout_typed_l rctx; *\) *)
(*       events *)
(*   in *)
(*   (\* _assert __FILE__ __LINE__ "refined event literals not bottom" *\) *)
(*   (\* @@ not *\) *)
(*   (\* @@ List.exists (fun (rctx, l) -> is_bot_literal ~rctx ~gvars:[] l) refined; *\) *)
(*   (\* let last = *\) *)
(*   (\*   match { events; op_filter } with *\) *)
(*   (\*   | { events = []; op_filter = `Whitelist [] } -> Choice.fail *\) *)
(*   (\*   | l -> *\) *)
(*   (\*       _assert __FILE__ __LINE__ "remaining literal not bottom" *\) *)
(*   (\*       @@ not *\) *)
(*   (\*       @@ is_bot_literal ~rctx ~gvars:[] l; *\) *)
(*   (\*       Choice.return (rctx, l) *\) *)
(*   (\* in *\) *)
(*   let* rctx, l = *)
(*     Choice.(of_list refined ++ return (rctx, { events; op_filter })) *)
(*   in *)
(*   let* () = Choice.guard @@ not @@ is_bot_literal ~rctx ~gvars:[] l in *)
(*   Choice.return (rctx, l) *)

let add_prop_to_rctx phi rctx =
  let fvs = fv_prop phi in
  match List.find_map (RTypectx.get_ty_opt rctx) fvs with
  | Some _ ->
      RTypectx.fold_right
        (fun (rx, rty) rctx ->
          let rty' =
            match rty with
            | BaseRty { cty } when StrList.exists rx fvs ->
                let phi = subst_prop_id (rx, cty.v.x) phi in
                BaseRty { cty = add_prop_to_cty phi cty }
            | _ -> rty
          in
          (rx, rty') :: rctx)
        rctx []
  | None ->
      RTypectx.new_to_right rctx
      @@ ((Rename.unique "u") #:: (mk_unit_rty_from_prop phi))

let rec collect_ghosts ?(substs = []) ?(rxs = []) ~i hty =
  (* ASSUMPTION: not all args are ghost *)
  let rty = hty_force_rty hty in
  match rty with
  | ArrRty { arr = GhostArr { x; ty }; rethty } ->
      let x' = x ^ string_of_int i in
      let rethty = subst_hty_id (x, x') rethty in
      collect_ghosts ~substs:((x, x') :: substs)
        ~rxs:((x' #:: (mk_top ty)) :: rxs)
        ~i rethty
  (* ASSUMPTION: ghost args are not allowed
     to be separated by normal args *)
  | ArrRty { arr = _; rethty = _ } -> (substs, rxs, hty)
  | BaseRty _ -> _failatwith __FILE__ __LINE__ "die"

let rec collect_args ?(rxs = []) hty =
  match hty with
  | Rty (ArrRty { arr = NormalArr rx; rethty }) ->
      collect_args ~rxs:(rx :: rxs) rethty
  | Rty (ArrRty { arr = ArrArr rty; rethty }) ->
      let f = Rename.unique "farg" in
      collect_args ~rxs:((f #:: rty) :: rxs) rethty
  | Rty (ArrRty { arr = GhostArr _; _ }) -> _failatwith __FILE__ __LINE__ "die"
  | _ -> (List.rev rxs, hty)

let rec hty_to_contract ?(phis = []) args hty =
  match (args, hty) with
  | [], _ -> (List.rev phis, hty)
  | arg :: args', Rty (ArrRty { arr = NormalArr { rx; rty }; rethty }) -> (
      match arg.x with
      | VVar x ->
          let _, phi = cty_typed_to_prop x #::: (rty_to_cty rty) in
          let rethty = subst_hty_id (rx, x) rethty in
          hty_to_contract ~phis:(phi :: phis) args' rethty
      | VConst c ->
          let cty = rty_to_cty rty in
          let phi = subst_prop (cty.v.x, AC c) cty.phi in
          let rethty = subst_hty (rx, AC c) rethty in
          hty_to_contract ~phis:(phi :: phis) args' rethty
      | VTu _ -> _failatwith __FILE__ __LINE__ "unimp"
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | _ :: args', Rty (ArrRty { arr = ArrArr _; rethty }) ->
      hty_to_contract ~phis args' rethty
  | _ -> _failatwith __FILE__ __LINE__ "die"
