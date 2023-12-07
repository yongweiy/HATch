include Baux
open Language
open TypedCoreEff
module RCtx = RTypectx
module ROpCtx = ROpTypectx
open Sugar
open Rty
(* open TypedCoreEff *)

let pprint_res_one (id, name, res, timef) =
  match res with
  | Some _ ->
      Printf.printf "Task %i(%s): exec time %f(s), type check succeeded\n" id
        name timef
  | None ->
      Printf.printf "Task %i(%s): exec time %f(s), type check failed\n" id name
        timef

(* symbolic value is proposition without quantifier
   TODO: is this okay?
*)
type sval = prop
type sfa_rel = [ `Sub | `NotSub ]

let string_of_sfa_rel = function `Sub -> "⊆" | `NotSub -> "⊈"

(* path constraint *)
type pc = {
  sfa : sfa;
  heap : (string, comp typed) Hashtbl.t; (* lambda & recursive *)
  vctx : (string, lit) Hashtbl.t;
      (* local variables, lit may and may only contain logical variables *)
  lctx : string typed list; (* logical variables *)
  (* subsumption to be checked between sfa *)
  sfa_constr : (sfa * [ `Sub | `NotSub ] * sfa) list;
  (* normal constraint *)
  constr : prop list;
}

let print_pc { sfa; heap; vctx; lctx; sfa_constr; constr } =
  List.iter
    (fun prop ->
      Env.show_debug_debug @@ fun _ -> Pp.printf "%s\n" @@ layout_prop prop)
    constr;
  List.iter
    (fun (sfa1, rel, sfa2) ->
      Env.show_debug_debug @@ fun _ ->
      Pp.printf "%s %s %s\n" (layout_regex sfa1) (string_of_sfa_rel rel)
        (layout_regex sfa2))
    sfa_constr

let pc_empty () =
  {
    sfa = EpsilonA;
    heap = Hashtbl.create 10;
    vctx = Hashtbl.create 10;
    lctx = [];
    sfa_constr = [];
    constr = [];
  }

let pc_with_sfa sfa pc = { pc with sfa }
let pc_intro_lvar x pc = { pc with lctx = x :: pc.lctx }
let pc_intro_lvars xs pc = { pc with lctx = xs @ pc.lctx }

let pc_bind_var (x, lit) pc =
  Hashtbl.add pc.vctx x lit;
  pc

let pc_is_feasible pc = Smtquery.check_sat_bool @@ smart_and pc.constr
let pc_concretize pc : 'a option = _failatwith __FILE__ __LINE__ "unimp"

type 'a res = { pc : pc; opt : 'a option }
(** None indicates aborted *)

let pc_assume constr pc =
  if is_true constr then pc else { pc with constr = constr :: pc.constr }

let pc_assume_sfa pc rel sfa =
  { pc with sfa_constr = (pc.sfa, rel, sfa) :: pc.sfa_constr }

let pc_assert pc phi : unit res Choice.t =
  Choice.of_list
    [
      { pc = pc_assume (Not phi) pc; opt = None };
      { pc = pc_assume phi pc; opt = Some () };
    ]

let pc_assert_sfa pc sfa : unit res Choice.t =
  Choice.of_list
    [
      { pc = pc_assume_sfa pc `NotSub sfa; opt = None };
      { pc = pc_assume_sfa pc `Sub sfa; opt = Some () };
    ]

let pc_abort pc = Choice.return { pc; opt = None }
let pc_append_sfa pc sfa = { pc with sfa = SeqA (pc.sfa, sfa) }

let pc_append_sfa_slow pc sfa =
  { pc with sfa = LandA (SeqA (pc.sfa, StarA AnyA), sfa) }

let ret pc v = Choice.return { pc; opt = Some v }
let ( let** ) x f = Choice.fair_bind f x
let ( let++ ) x f = Choice.fmap f x

let ( let*+ ) x f =
  Choice.fair_bind
    (function
      | { pc; opt = Some a } -> f (pc, a)
      | { pc; opt = None } as res -> Choice.return res)
    x

let value_to_lit file line vctx (v : value typed) : lit typed =
  (match v.x with
  | VVar name -> Hashtbl.find vctx name
  | VConst c -> AC c
  | VLam _ -> _failatwith file line "?"
  | VFix _ -> _failatwith file line "?"
  | VTu _ -> _failatwith file line "?")
  #: v.ty

let is_new_adding (pre, post) =
  match post with
  | SeqA (post1, post2) -> if eq pre post1 then Some post2 else None
  | _ -> None

(* introduce logical variable for ghost variables *)
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

(* TOOD:
   top level does not have to be CVal
   VFix case? on-demand unrolling?
*)
let rec collect_args pc ({ hx = comp; hty } as hcomp) =
  match comp with
  | CVal f -> (
      match f with
      | VFix _ -> _failatwith __FILE__ __LINE__ "recursive unimp"
      | VLam { lamarg; lambody } -> (
          let rty = hty_force_rty hty in
          let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
          let lvar = Rename.unique_with_prefix lamarg.x "l" in
          match arr with
          | NormalArr x ->
              let pc = pc_intro_lvar lvar #: (erase_rty x.rty) pc in
              let pc = pc_bind_var (lamarg.x, AVar lvar) pc in
              let rethty = subst_hty_id (x.rx, lamarg.x) rethty in
              collect_args pc { hx = lambody.x; hty = rethty }
          | ArrArr _ -> _failatwith __FILE__ __LINE__ "higher-order unimp"
          | GhostArr _ -> _failatwith __FILE__ __LINE__ "die")
      | VConst _ | VVar _ | VTu _ -> _failatwith __FILE__ __LINE__ "die")
  | _ -> (pc, hcomp)

(** TODO: renaming arg when impose constraint *)
let exec_appop typectx pc (op, args) =
  let op_rty = ROpCtx.get_ty typectx.opctx op.x in
  let ghosts, op_hty = collect_ghosts (Rty op_rty) in
  let rec exec_args (cres : hty res Choice.t) = function
    | [] -> cres
    | arg :: args -> (
        let*+ pc, hty = cres in
        let rty = hty_force_rty hty in
        let arr, rethty = rty_destruct_arr __FILE__ __LINE__ rty in
        match arr with
        | NormalArr x ->
            (* TODO rename *)
            let lit = value_to_lit __FILE__ __LINE__ pc.vctx arg in
            let { v; phi } = rty_force_cty x.rty in
            let phi = subst_prop (v.x, lit.x) phi in
            let*+ pc, () = pc_assert pc phi in
            let rethty = subst_hty (x.rx, lit.x) rethty in
            Env.show_debug_debug (fun _ ->
                Pp.printf "rethty:\n%s\n" (layout_hty rethty));
            let res = ret pc rethty in
            exec_args res args
        | GhostArr { x; ty } ->
            let x' = Rename.unique x in
            let rethty = subst_hty_id (x, x') rethty in
            let pc = pc_intro_lvar x' #: ty pc in
            let res = ret pc rethty in
            exec_args res args
        | ArrArr rty ->
            _failatwith __FILE__ __LINE__ "higher-order unimplemented")
  in
  exec_args (ret pc op_hty) args

let rec exec (typectx : typectx) (pc : pc) (unrolled : comp typed) :
    value typed res Choice.t =
  let before_info line rulename =
    print_exec_info __FUNCTION__ line rulename typectx unrolled pc.sfa
  in
  let end_info line rulename is_valid =
    print_typing_rule __FUNCTION__ line "exec"
      (spf "%s [%s]" rulename
         (match is_valid with Some _ -> "✓" | None -> "𐄂"));
    is_valid
  in
  match unrolled.x with
  | CVal v -> ret pc v #: unrolled.ty
  | CLetE { lhs; rhs; letbody } ->
      Env.show_debug_debug (fun _ -> Pp.printf "rhs:\n%s\n" (layout_comp rhs));
      let*+ pc, hty =
        match rhs.x with
        | CVal v ->
            (* TODO: only constant and var is handled *)
            let lit = value_to_lit __FILE__ __LINE__ pc.vctx v #: rhs.ty in
            let hty = Rty (mk_rty_var_eq_lit lit.ty lit.x) in
            ret pc hty
        | CApp { appf; apparg } ->
            _failatwith __FILE__ __LINE__ "function application unimplemented"
        | CAppOp { op; appopargs } -> (
            match op.x with
            | Op.BuiltinOp _ -> exec_appop typectx pc (op, appopargs)
            | Op.DtOp _ -> _failatwith __FILE__ __LINE__ "die"
            | Op.EffOp _ -> exec_appop typectx pc (op, appopargs))
        | _ ->
            Printf.printf "ERR:\n%s\n" (layout_comp rhs);
            _failatwith __FILE__ __LINE__ "die"
      in
      let lvar = Rename.unique_with_prefix lhs.x "l" in
      let pc = pc_bind_var (lhs.x, AVar lvar) pc in
      (* pc |> pc_add_constr phi |> pc_intro_lvar lvar |> Option.some *)
      let rec branch : hty -> unit res Choice.t = function
        | Rty (BaseRty { cty }) ->
            let lvar, phi = cty_typed_to_prop lvar #::: cty in
            let pc = pc |> pc_intro_lvar lvar |> pc_assume phi in
            ret pc ()
        | Rty (ArrRty _ as rty) ->
            Env.show_debug_debug (fun _ -> Pp.printf "%s\n" (layout_rty rty));
            _failatwith __FILE__ __LINE__ @@ "higher-order unimp"
        | Htriple { pre; resrty; post } -> (
            let*+ pc, () = branch (Rty resrty) in
            let*+ pc, () = pc_assert_sfa pc pre in
            match is_new_adding (pre, post) with
            | Some post -> ret (pc_append_sfa pc post) ()
            | None -> ret (pc_append_sfa_slow pc post) ())
        | Inter (hty1, hty2) -> Choice.(branch hty1 <|> branch hty2)
      in
      let*+ pc, () = branch hty in
      exec typectx pc letbody
  | CMatch
      {
        matched;
        match_cases =
          [
            { constructor = ctrue; args = _; exp = branch_true };
            { constructor = cfalse; args = _; exp = branch_false };
          ];
      } ->
      assert (String.equal ctrue.x "True");
      assert (String.equal cfalse.x "False");
      let matched_lit = value_to_lit __FILE__ __LINE__ pc.vctx matched in
      let phi_true =
        Lit (mk_lit_eq_lit matched_lit.ty matched_lit.x mk_lit_true)
      in
      let phi_false =
        Lit (mk_lit_eq_lit matched_lit.ty matched_lit.x mk_lit_false)
      in
      Choice.(
        exec typectx (pc_assume phi_true pc) branch_true
        <|> exec typectx (pc_assume phi_false pc) branch_false)
  | CMatch { matched; match_cases } ->
      (* Env.show_debug_debug (fun _ -> Pp.printf "%s\n" (layout_comp unrolled)); *)
      assert (List.length match_cases == 2);
      let ctrue = (List.hd match_cases).constructor.x in
      let cfalse = (List.nth match_cases 1).constructor.x in
      _failatwith __FILE__ __LINE__ ("non-boolean match unimp" ^ ctrue ^ cfalse)
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CErr ->
      (* TODO: what's its construct in surface language *)
      pc_abort pc

(* symbolic execute every path up to a certain bound *)
let check (opctx', rctx') structure normalized_structure =
  let opctx, rctx = ROpCtx.from_code structure in
  let opctx, rctx = (opctx' @ opctx, rctx' @ rctx) in
  let tasks = RTypectx.get_task structure in
  let ress =
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
        | None ->
            failwith "cannot find the implemetation of the given assertion"
        | Some (_, comp) ->
            let () =
              if not (Nt.eq comp.ty (erase_rty rty)) then
                let () =
                  Printf.printf
                    "The erased type of the refinement type mismacted the \
                     implementation:\n\
                     %s (rty) !=\n\
                     %s (imp)\n"
                    (Nt.layout (erase_rty rty))
                    (Nt.layout comp.ty)
                in
                _failatwith __FILE__ __LINE__ "input error"
              else ()
            in
            Env.show_debug_debug (fun _ -> Pp.printf "%s\n" (layout_comp comp));
            let ghosts, hty = collect_ghosts (Rty rty) in
            let pc = pc_empty () in
            let pc, hbody = collect_args pc { hx = comp.x; hty } in
            (* let typectx, unrolled, { pre; resrty; post } = *)
            (*   drop_args { rctx; opctx; introduced_gvars = [] } comp rty *)
            (* in *)
            hty_to_triples hbody.hty
            |> List.iter (fun (pre, resrty, post) ->
                   let hbody = hbody.hx #: (erase_hty hbody.hty) in
                   let exec_time, paths =
                     Sugar.clock (fun () ->
                         let*+ pc, v =
                           exec { rctx; opctx } (pc_with_sfa pre pc) hbody
                         in
                         let*+ pc, () = pc_assert_sfa pc post in
                         ret pc v)
                   in
                   let paths =
                     Choice.filter (fun { pc; opt } -> pc_is_feasible pc) paths
                   in
                   Choice.iter paths (fun { pc; opt } ->
                       print_pc pc;
                       Pp.printf "--------\n";
                       true))
        (* let if_type_checked = *)
        (*   match res with Some () -> true | None -> false *)
        (* in *)
        (* let () = *)
        (*   Env.show_debug_typing @@ fun _ -> *)
        (*   pprint_res_one (id, name, res, typecheck_time) *)
        (* in *)
        (* let () = Stat.settTypeCheck (if_type_checked, typecheck_time) in *)
        (* (id, name, res, typecheck_time)) *))
      tasks
  in
  ress
