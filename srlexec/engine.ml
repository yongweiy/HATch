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

module Builder (ExecBound : IntT) (AccelBound : IntT) (Config : Config.T) =
struct
  let apply ~i ~lhs ~letbody rty args cfg =
    let cfg = Config.with_comp letbody cfg in
    let substs_ghost, ghosts, hty = collect_ghosts ~i @@ Rty rty in
    let cfg = Config.add_rxs ghosts cfg in
    let substs_arg, phis, rethty = hty_to_contract args hty in
    let substs = substs_ghost @ substs_arg in
    let* cfg = Config.asserts phis cfg in
    match rethty with
    | Rty retrty -> C.return @@ Config.add_rx lhs.x #:: retrty cfg
    | _ -> (
        let* sfa_pre, retrty, sfa_post = C.of_list @@ hty_to_triples rethty in
        let* cfg = Config.admit ~substs sfa_pre cfg in
        let cfg = Config.add_rx lhs.x #:: retrty cfg in
        match sfa_post with
        | SeqA (sfa_pre', sfa_eff) ->
            _assert __FILE__ __LINE__ "die" (equal_sfa sfa_pre sfa_pre');
            Config.append ~substs sfa_eff cfg
        | _ when SRL.entails (sfa_pre, sfa_post) -> C.return cfg
        | _ -> _failatwith __FILE__ __LINE__ "unimp")

  let rec reduce ~until_rec ~i ~(opctx : ROpTypectx.ctx) (cfg : Config.config) =
    match (Config.comp cfg).x with
    | CErr | CVal _ -> C.return cfg
    | CLetE { lhs; rhs; letbody } -> (
        match rhs.x with
        | CErr -> C.return @@ Config.with_comp CErr #: letbody.ty cfg
        | CVal v ->
            let comp = do_subst_comp (lhs.x, v #: rhs.ty) letbody in
            C.return @@ Config.with_comp comp cfg
        | CApp { appf; apparg } -> (
            match appf.x with
            | VVar f ->
                let f_rty = Config.get_rty f cfg in
                apply ~i ~lhs ~letbody f_rty [ apparg ] cfg
            | VLam { lamarg; lambody } ->
                let lambody =
                  lambody
                  |> do_subst_comp (lamarg.x, apparg)
                  |> rename_comp ~f:(fun x -> x ^ "_" ^ string_of_int i)
                in
                let comp = mk_lete lhs lambody letbody in
                C.return @@ Config.with_comp comp cfg
            | VFix { fixname; fixarg; fixbody } when until_rec -> C.return cfg
            | VFix { fixname; fixarg; fixbody } ->
                let summarized =
                  let* iter_info, cfg_i = Config.start_iteration cfg in
                  let* cfg_j =
                    reduce_repeat ~n:AccelBound.value ~start:i ~opctx cfg_i
                  in
                  Config.end_iteration iter_info cfg_j
                in
                let fixbody =
                  fixbody
                  |> do_subst_comp (fixname.x, appf)
                  |> do_subst_comp (fixarg.x, apparg)
                  |> rename_comp ~f:(fun x -> x ^ "_" ^ string_of_int i)
                in
                let inlined = mk_lete lhs fixbody letbody in
                C.mplus summarized @@ C.return @@ Config.with_comp inlined cfg
            | VTu _ | VConst _ -> _failatwith __FILE__ __LINE__ "die")
        | CAppOp { op; appopargs } ->
            let op_rty = ROpTypectx.get_ty opctx op.x in
            apply ~i ~lhs ~letbody op_rty appopargs cfg
        | CLetE _ | CMatch _ ->
            let+ cfg =
              reduce ~until_rec ~i ~opctx @@ Config.with_comp rhs cfg
            in
            let comp = mk_lete lhs (Config.comp cfg) letbody in
            Config.with_comp comp cfg
        | CLetDeTu _ -> _failatwith __FILE__ __LINE__ "unimp")
    | CMatch { matched; match_cases } ->
        (* ASSUMPTION: let's say patterns are disjoint *)
        let^ { constructor; args; exp } = C.of_list match_cases in
        let pat, rxs =
          if String.equal constructor.x "True" then (AC (Const.B true), [])
          else if String.equal constructor.x "False" then
            (AC (Const.B false), [])
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

  (** Naively Incrementally Hatch Bug
    TODO: make it more liberal to avoid repeated concretization of Choice Monad
 *)

  and reduce_repeat ?(mode = `PassThrough) ~n ?(start = 0) ~opctx cfgs =
    let rec aux i cfg =
      if i > n then C.return cfg
      else
        C.fair_bind (aux (i + 1))
        @@
        match mode with
        | `PassThrough -> reduce ~until_rec:true ~i:(start + i) ~opctx cfg
        | `TopLevel _ ->
            C.fmap (Config.hatch ~mode)
            @@ reduce ~until_rec:false ~i:(start + i) ~opctx cfg
    in
    aux 0 cfgs

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
    let opctx, rctx0 = (opctx' @ opctx, rctx' @ rctx) in
    RTypectx.get_task structure
    |> List.mapi (fun id (name, rty) ->
           let id = id + 1 in
           let () =
             MetaConfig.show_debug_typing @@ fun _ ->
             Pp.printf "@{<bold>Task %i:@}\n" id
           in
           match List.assoc_opt ~eq:String.equal name normalized_structure with
           | None ->
               failwith "cannot find the implemetation of the given assertion"
           | Some comp ->
               let exec_time, res =
                 Sugar.clock (fun () ->
                     let substs, rxs, comp, hty = wrap_client comp rty in
                     let rctx = RTypectx.new_to_rights rctx0 rxs in
                     hty_to_triples hty
                     |> List.find_opt (fun (sfa_pre, retrty, sfa_post) ->
                            try
                              Limit.run_with_memory_limit 1000000000
                              @@ fun () ->
                              ignore @@ C.to_list
                              @@ C.bind
                                   (reduce_repeat
                                      ~mode:(`TopLevel (retrty, sfa_post))
                                      ~opctx ~n:ExecBound.value)
                              @@ Config.init ~substs rctx sfa_pre comp sfa_post;
                              true
                            with
                            | Config.PreemptiveHatch cfg ->
                                Pp.printf "@{<bold>Preemptive Hatch@}\n";
                                Config.print_config
                                  ~chop_rctx:(List.length rctx0) cfg;
                                false
                            | Config.TerminatedHatch cfg ->
                                Pp.printf "@{<bold>Terminated Hatch@}\n";
                                Config.print_config
                                  ~chop_rctx:(List.length rctx0) cfg;
                                false
                            | Out_of_memory ->
                                Printf.printf "Out of memory: ";
                                false))
               in
               Config.output_dot name;
               (id, name, res, exec_time))
end
