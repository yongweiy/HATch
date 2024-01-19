open Zzdatatype.Datatype
open Language
open TypedCoreEff
open Sugar
open Rty
module RCtx = RTypectx
module C = Choice
module L = Literal
module D = Deriv
module S = Sample

let ( let* ) x f = Choice.bind f x
let ( let+ ) x f = Choice.map f x
let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type state = {
  (* the trace is stored in reverse order *)
  tr : L.literal list;
  post : regex;
  rctx : RCtx.ctx;
  gvars : string typed list;
}

let layout_state { tr; post; rctx; gvars } =
  String.concat "\n"
    [
      "trace:";
      String.concat " -> " @@ List.map L.layout_literal @@ List.rev tr;
      "post:";
      Rty.layout_regex post;
      "rctx:";
      RTypectx.layout_typed_l rctx;
      "gvars:";
      String.concat ", " @@ List.map (layout_typed Fun.id) gvars;
    ]

type 'a result = { st : state; res : 'a option }

let ( let** ) (x : 'a result C.t) (f : state * 'a -> 'b result C.t) =
  let* res = x in
  match res with
  | { st; res = Some res } -> f (st, res)
  | { st; res = None } -> C.return { st; res = None }

let ret st res = C.return { st; res = Some res }
let abort st = C.return { st; res = None }

(* let ( let++ ) x f = *)
(*   let+ { st; res } = x in *)
(*   match res with Some a -> { st; res = Some (f a) } | None -> { st; res } *)
(* let map_res f = function *)
(*   | { st; res = Some res } -> C.return { st; res = Some (f res) } *)
(*   | { st; res = None } -> C.return { st; res = None } *)

type mstate = state C.t

let init_state tr post = { tr; post; rctx = []; gvars = [] }
let bind_var binding st = { st with rctx = RCtx.new_to_right st.rctx binding }
let intro_gvar gvar st = { st with gvars = gvar :: st.gvars }

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
      @@ ((Rename.unique "a") #:: (mk_unit_rty_from_prop phi))

let assume_prop phi st =
  if is_true phi then st else { st with rctx = add_prop_to_rctx phi st.rctx }

let assert_prop phi st res =
  let false_branch =
    if is_true phi then C.fail else abort (assume_prop (mk_not phi) st)
  in
  let true_branch = ret (assume_prop phi st) res in
  C.mplus false_branch true_branch

let absorb_pre ?(bound = 1) pre st =
  let rctx, gvars = (st.rctx, st.gvars) in
  let aux res =
    let* pre, st = res in
    let* l, pre = S.uncons_regex ~rctx ~gvars pre in
    let+ l, post = D.symb_deriv ~rctx ~gvars l st.post in
    (* no guard to ensure post is nullable since it is unlikely *)
    (pre, { st with tr = l :: st.tr; post })
  in
  let rec loop bound (res : (sfa * state) C.t) =
    (* Pp.printf "loop: %d\n" bound; *)
    (* Choice.iter res (fun (pre, st) -> *)
    (*     Pp.printf "trace:\n"; *)
    (*     L.print_trace st.tr; *)
    (*     Pp.printf "post:\n%s\n" @@ Rty.layout_regex st.post; *)
    (*     true); *)
    if bound = 0 then res else C.mplus res @@ loop (bound - 1) (aux res)
  in
  let* pre, st = loop bound (C.return (pre, st)) in
  let* () = C.guard @@ D.is_nullable pre in
  C.return st

(** check pre-condition SFA of method calls against current program
    state, i.e., `tr` and `rctx`.

    TODO: relax the restriction that `new_gvars` may only be used as
    operands of equality in qualifiers of `pre`, and each variable may
    only appear once to avoid entanglement of different parts of
    `pre`.
*)
let check_pre ghosts pre st =
  let rctx, gvars = (st.rctx, st.gvars) in
  List.fold_right
    (fun lit ress ->
      let* tr_rev, regex, rxs = ress in
      let* lit', regex', rxs' =
        D.symb_deriv_with_ghosts ~rctx ~gvars ~ghosts lit regex
      in
      (* TODO: try pushing guard to the end *)
      let* () = C.guard @@ D.is_nullable regex' in
      C.return (lit' :: tr_rev, regex', rxs @ rxs'))
    st.tr
    (Choice.return ([], pre, []))

let is_new_adding (pre, post) =
  match post with
  | SeqA (post1, post2) -> if eq pre post1 then Some post2 else None
  | _ -> None

let rec collect_ghosts ?(ghosts = []) hty =
  let rty = hty_force_rty hty in
  match rty with
  | ArrRty { arr = NormalArr _ | ArrArr _; rethty = _ } -> (ghosts, hty)
  | ArrRty { arr = GhostArr { x; ty }; rethty } ->
      let x' = Rename.unique x in
      let rethty = subst_hty_id (x, x') rethty in
      let ghosts = (x' #: ty) :: ghosts in
      collect_ghosts ~ghosts rethty
  | BaseRty _ -> _failatwith __FILE__ __LINE__ "die"

let unify_var_arr_ret y (arr, rethty) =
  match arr with
  | NormalArr x ->
      let rethty = subst_hty_id (x.rx, y) rethty in
      ({ rx = y; rty = x.rty }, rethty)
  | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
  | ArrArr _ -> _failatwith __FILE__ __LINE__ "higher-order unimp"

let unify_var_func_rty y hty =
  let arr, rethty = rty_destruct_arr __FILE__ __LINE__ hty in
  unify_var_arr_ret y (arr, rethty)

let rec collect_args rctx ({ hx = comp; hty } as hcomp) =
  match comp with
  | CVal (VFix _) -> _failatwith __FILE__ __LINE__ "recursive unimp"
  | CVal (VLam { lamarg; lambody }) ->
      let rty = hty_force_rty hty in
      let rarg, rethty = unify_var_func_rty lamarg.x rty in
      collect_args
        (RCtx.new_to_right rctx rarg)
        { hx = lambody.x; hty = rethty }
  | CVal (VConst _ | VVar _ | VTu _) -> (rctx, hcomp)
  | _ -> (rctx, hcomp)

let value_to_rty file line rctx (v : value typed) : rty =
  match v.x with
  | VVar name -> RTypectx.get_ty rctx name
  | VConst c -> mk_rty_var_eq_c v.ty c
  | VLam _ -> _failatwith file line "?"
  | VFix _ -> _failatwith file line "?"
  | VTu _ -> _failatwith file line "?"

(* TODO: only constant and variable is supported *)
let value_to_lit file line = function
  | VVar name -> AVar name
  | VConst c -> AC c
  | VLam _ -> _failatwith file line "?"
  | VFix _ -> _failatwith file line "?"
  | VTu _ -> _failatwith file line "?"

let exec_appop opctx st (op, args) : rty result C.t =
  let op_rty = ROpTypectx.get_ty opctx op.x in
  let ghosts, op_hty = collect_ghosts (Rty op_rty) in
  (* TODO: collect constraint on ghosts from `st.tr`*)
  let exec_arg st hty arg =
    let rty = hty_force_rty hty in
    let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
    match arr with
    | NormalArr x ->
        let lit = value_to_lit __FILE__ __LINE__ arg.x in
        let { v; phi } = rty_force_cty x.rty in
        let phi = subst_prop (v.x, lit) phi in
        let rethty = subst_hty (x.rx, lit) rethty in
        Env.show_debug_debug (fun _ ->
            Pp.printf "rethty:\n%s\n" (layout_hty rethty));
        assert_prop phi st rethty
    | GhostArr { x; ty } ->
        _failatwith __FILE__ __LINE__ "die"
        (* let x' = Rename.unique x in *)
        (* ret (intro_gvar x' #: ty st) (subst_hty_id (x, x') rethty) *)
    | ArrArr rty -> _failatwith __FILE__ __LINE__ "higher-order unimp"
  in
  let** st, hty =
    List.fold_left
      (fun mres arg ->
        let** st, hty = mres in
        exec_arg st hty arg)
      (ret st op_hty) args
  in
  match hty with
  | Rty rty ->
      _assert __FILE__ __LINE__ "base rty" @@ is_base_rty rty;
      ret st rty
  | _ -> (
      let ghosts = List.map (fun g -> g.x) ghosts in
      let* pre, resrty, post = C.of_list @@ hty_to_triples hty in
      (* TODO: what if all pre-condition fails *)
      let* tr, _pre, rxs = check_pre ghosts pre st in
      let st = { st with tr; rctx = RTypectx.new_to_rights st.rctx rxs } in
      (* Pp.printf "%s\n" @@ RTypectx.layout_typed_l st.rctx; *)
      (* TODO: collect constraint on ghost varibles from `pre` and `st.tr` *)
      match is_new_adding (pre, post) with
      | Some post ->
          let+ st = absorb_pre post st in
          { st; res = Some resrty }
      | None -> _failatwith __FILE__ __LINE__ "die")

(* exec_args { st; res = Some op_hty } args *)

let rec exec_typed_unrolled opctx (st : state) comp =
  match comp.x with
  | CVal v -> ret st v #: comp.ty
  | CLetE { lhs; rhs; letbody } ->
      let** st, rty =
        match rhs.x with
        | CVal value ->
            ret st @@ mk_rty_var_eq_lit rhs.ty
            @@ value_to_lit __FILE__ __LINE__ value
        | CApp { appf; apparg } ->
            _failatwith __FILE__ __LINE__ "function application unimp"
        | CAppOp { op; appopargs } -> (
            match op.x with
            | Op.BuiltinOp _ -> exec_appop opctx st (op, appopargs)
            | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
            | Op.EffOp _ -> exec_appop opctx st (op, appopargs))
        | _ ->
            Printf.printf "ERR:\n%s\n" (layout_comp rhs);
            _failatwith __FILE__ __LINE__ "die"
      in
      exec_typed_unrolled opctx (bind_var lhs.x #:: rty st) letbody
  | CMatch
      {
        matched;
        match_cases =
          [
            { constructor = ctrue; args = _; exp = branch_true };
            { constructor = cfalse; args = _; exp = branch_false };
          ];
      }
    when String.equal ctrue.x "True" && String.equal cfalse.x "False" ->
      let lit = value_to_lit __FILE__ __LINE__ matched.x in
      let* phi, branch =
        C.of_list [ (Lit lit, branch_true); (Not (Lit lit), branch_false) ]
      in
      exec_typed_unrolled opctx (assume_prop phi st) branch
  | CMatch { matched; match_cases } ->
      (* Env.show_debug_debug (fun _ -> Pp.printf "%s\n" (layout_comp unrolled)); *)
      assert (List.length match_cases == 2);
      let ctrue = (List.hd match_cases).constructor.x in
      let cfalse = (List.nth match_cases 1).constructor.x in
      _failatwith __FILE__ __LINE__ ("non-boolean match unimp" ^ ctrue ^ cfalse)
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CErr -> abort st

let exec_htyped_func opctx comp =
  Pp.printf "prog:\n%s\n" @@ layout_comp @@ (comp.hx #: (erase_hty comp.hty));
  let gvars, hty = collect_ghosts comp.hty in
  let rctx, hbody = collect_args [] { hx = comp.hx; hty } in
  let body = hbody.hx #: (erase_hty hbody.hty) in
  (* TODO: check `resrty` *)
  let* pre, resrty, post = Choice.of_list @@ Rty.hty_to_triples hbody.hty in
  let* st = absorb_pre pre { tr = []; post; rctx; gvars } in
  L.print_trace st.tr;
  Pp.printf "before:\n%s\n" (layout_regex st.post);
  let+ { st; res } = exec_typed_unrolled opctx st body in
  Pp.printf "\n%s\n" @@ layout_state st;
  Option.iter (fun value -> Pp.printf "value: %s\n" @@ layout_value value) res;
  match res with
  | Some value ->
      let rty = value_to_rty __FILE__ __LINE__ st.rctx value in
      Subtyping.sub_rty_bool st.rctx (rty, resrty) && D.is_nullable st.post
  | None -> Subtyping.is_bot_cty st.rctx @@ mk_unit_from_prop mk_true

let check (opctx', rctx') structure normalized_structure =
  let opctx, rctx = ROpTypectx.from_code structure in
  let opctx, rctx = (opctx' @ opctx, rctx' @ rctx) in
  let tasks = RTypectx.get_task structure in
  List.mapi
    (fun id (name, rty) ->
      let id = id + 1 in
      let () =
        Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
      in
      match
        List.find_opt
          (fun (name', _) -> String.equal name name')
          normalized_structure
      with
      | None -> failwith "cannot find the implemetation of the given assertion"
      | Some (_, comp) ->
          let exec_time, res =
            Sugar.clock (fun () ->
                C.forall
                @@ exec_htyped_func opctx { hx = comp.x; hty = Rty rty })
          in
          let res = if res then Some () else None in
          (id, name, res, exec_time))
    tasks
