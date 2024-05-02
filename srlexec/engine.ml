open Zzdatatype.Datatype
(** entry point of the symbolic execution engine
    
    TODO: make it a functor that is parameterized
    by a `Config` module to enable easy ablation *)

open Language
open TypedCoreEff
open Sugar
open Rty
open Utils
module RCtx = RTypectx
module C = Choice
module L = Literal
module D = Deriv
module Tr = Trace

let rec reduce ~i ~(opctx : ROpTypectx.ctx) (cfg : Config.config) =
  match cfg.comp.x with
  | CErr | CVal _ -> C.return cfg
  | CLetE { lhs; rhs; letbody } -> (
      match rhs.x with
      | CErr -> C.return @@ Config.with_comp CErr #: letbody.ty cfg
      | CVal v ->
          let comp = do_subst_comp (lhs.x, v #: rhs.ty) letbody in
          C.return @@ Config.with_comp comp cfg
      | CApp { appf; apparg } -> (
          match appf.x with
          | VVar f -> _failatwith __FILE__ __LINE__ "higher-order unimp"
          | VLam { lamarg; lambody } ->
              let lambody = do_subst_comp (lamarg.x, apparg) lambody in
              let comp = mk_lete lhs lambody letbody in
              C.return @@ Config.with_comp comp cfg
          | VFix { fixname; fixarg; fixbody } ->
              let fixbody =
                fixbody
                |> do_subst_comp (fixname.x, appf)
                |> do_subst_comp (fixarg.x, apparg)
                |> rename_comp ~f:(fun x -> x ^ "_" ^ string_of_int i)
              in
              let comp = mk_lete lhs fixbody letbody in
              C.return @@ Config.with_comp comp cfg
          | VTu _ | VConst _ -> _failatwith __FILE__ __LINE__ "die")
      | CAppOp { op; appopargs } -> (
          let cfg = Config.with_comp letbody cfg in
          let op_rty = ROpTypectx.get_ty opctx op.x in
          let substs_ghost, ghosts, hty = collect_ghosts ~i @@ Rty op_rty in
          let cfg = Config.add_rxs ghosts cfg in
          let substs_arg, phis, rethty = hty_to_contract appopargs hty in
          let substs = substs_ghost @ substs_arg in
          let* cfg = Config.asserts phis cfg in
          match rethty with
          | Rty retrty -> C.return @@ Config.add_rx lhs.x #:: retrty cfg
          | _ ->
              let* sfa_pre, retrty, sfa_post =
                C.of_list @@ hty_to_triples rethty
              in
              let[@warning "-8"] (SeqA (sfa_pre', sfa_new)) = sfa_post in
              _assert __FILE__ __LINE__ "die" (equal_sfa sfa_pre sfa_pre');
              let* cfg = Config.admit ~substs sfa_pre cfg in
              let cfg = Config.add_rx lhs.x #:: retrty cfg in
              Config.append ~substs sfa_new cfg)
      | CLetE _ | CMatch _ ->
          let+ cfg = reduce ~i ~opctx @@ Config.with_comp rhs cfg in
          let rhs = cfg.comp in
          let comp = mk_lete lhs rhs letbody in
          Config.with_comp comp cfg
      | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp")
  | CMatch { matched; match_cases } ->
      (* ASSUMPTION: let's say patterns are disjoint *)
      let^ { constructor; args; exp } = C.of_list match_cases in
      let pat, rxs =
        if String.equal constructor.x "True" then (AC (Const.B true), [])
        else if String.equal constructor.x "False" then (AC (Const.B false), [])
        else
          let ctor = Op.mk_dt_op #-> constructor in
          let xs = List.map (( #-> ) Rename.unique) args in
          let rxs = List.map (fun x -> x.x #:: (Rty.mk_top x.ty)) xs in
          let args = List.map (( #-> ) (fun x -> AVar x)) xs in
          (AAppOp (ctor, args), rxs)
      in
      (* ASSUMPTION: `matched` is first-order *)
      let matched = _value_to_lit __FILE__ __LINE__ matched in
      let phi = mk_prop_lit_eq_lit matched.ty matched.x pat in
      cfg |> Config.with_comp exp |> Config.add_rxs rxs |> Config.assume phi
  | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp"
  | CAppOp _ | CApp _ -> _failatwith __FILE__ __LINE__ "not in MNF"

(** Naively Incrementally Hatch Bug
    TODO: make it more liberal to avoid repeated concretization of Choice Monad
 *)
(* let reduce_until_hatched ~opctx ~retrty cfgs = *)
(*   let rec aux cfgs = *)
(*     let cfgs = C.fmap (Config.hatch ~retrty) cfgs in *)
(*     D.G.output @@ open_out "deriv.dot"; *)
(*     C.iter cfgs (fun cfg -> *)
(*         Pp.printf "----\n"; *)
(*         Config.print_config cfg; *)
(*         true); *)
(*     Pp.printf "--------------------------------------\n"; *)
(*     if C.is_empty cfgs then C.fail *)
(*     else *)
(*       let witnesses = C.fmap Config.get_witness cfgs in *)
(*       if not @@ C.is_empty witnesses then witnesses *)
(*       else aux @@ C.bind (reduce ~opctx) cfgs *)
(*   in *)
(*   aux cfgs *)

let reduce_repeat ?(n = 20) ~opctx ~retrty cfgs =
  let rec aux i =
    if i = n then Fun.id else C.bind (aux (i + 1) << reduce ~i ~opctx)
  in
  aux 0 cfgs |> C.fmap @@ Config.hatch ~retrty |> C.fmap Config.get_witness

let wrap_client comp rty =
  let rec apply_args v = function
    | [] -> mk_val v
    | arg :: args ->
        let f' = Rename.unique "f" in
        let ty = Nt.get_retty v.ty in
        mk_lete f' #: ty (mk_app v arg) (apply_args (VVar f') #: ty args)
  in
  let substs, ghosts, hty = collect_ghosts ~i:0 @@ Rty rty in
  let args, hty = collect_args hty in
  let rxs = ghosts @ args in
  let args = List.map (fun rx -> (VVar rx.rx) #: (erase_rty rx.rty)) args in
  let comp' = apply_args (to_v comp) args in
  (substs, rxs, comp', hty)

let main (opctx', rctx') structure normalized_structure =
  let opctx, rctx = ROpTypectx.from_code structure in
  let opctx, rctx = (opctx' @ opctx, rctx' @ rctx) in
  RTypectx.get_task structure
  |> List.mapi (fun id (name, rty) ->
         let id = id + 1 in
         let () =
           Env.show_debug_typing @@ fun _ -> Pp.printf "@{<bold>Task %i:@}\n" id
         in
         match List.assoc_opt name normalized_structure with
         | None ->
             failwith "cannot find the implemetation of the given assertion"
         | Some comp ->
             let exec_time, res =
               Sugar.clock (fun () ->
                   let substs, rxs, comp, hty = wrap_client comp rty in
                   hty_to_triples hty
                   |> List.find_opt (fun (sfa_pre, retrty, sfa_post) ->
                          let witnesses =
                            C.to_list
                            @@ reduce_repeat ~opctx ~retrty
                            @@ Config.init ~substs rxs sfa_pre comp sfa_post
                          in
                          List.iter Config.print_witness witnesses;
                          List.is_empty witnesses))
             in
             D.G.output @@ open_out @@ name ^ ".dot";
             (id, name, res, exec_time))
