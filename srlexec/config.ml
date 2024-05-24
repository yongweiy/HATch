open Zzdatatype.Datatype
open Language
open TypedCoreEff
open Rty
open Sugar
open Utils
open Deriv
module C = Choice
module L = Literal
module Tr = Trace

module type T = sig
  type config

  val layout_config : config -> string
  val print_config : config -> unit

  val init :
    substs:(string * string) list ->
    RTypectx.ctx ->
    sfa ->
    comp typed ->
    sfa ->
    config C.t

  val comp : config -> comp typed
  val with_comp : comp typed -> config -> config
  val get_rty : string -> config -> rty
  val add_rx : string rtyped -> config -> config
  val add_rxs : string rtyped list -> config -> config
  val abort : config -> config option
  val assume : prop -> config -> config option
  val assert_ : prop -> config -> config option
  val asserts : prop list -> config -> config C.t
  val admit : substs:(string * string) list -> sfa -> config -> config C.t
  val append : substs:(string * string) list -> sfa -> config -> config C.t
  val reach_bad_state : config -> bool
  val hatch : retrty:rty -> sfa_post:sfa -> config -> config option
  val output_dot : string -> unit

  type iteration_info

  val start_iteration : config -> (iteration_info * config) C.t
  val end_iteration : iteration_info -> config -> config C.t

  type witness

  val print_witness : witness -> unit
  val get_witness : config -> witness option
end

module Naive : T = struct
  type config = { rctx : RTypectx.ctx; curr : sfa; comp : comp typed }

  let layout_config { rctx; curr; comp } =
    String.concat "\n"
      [
        "rctx = " ^ RTypectx.layout_typed_l rctx;
        "curr = " ^ layout_regex curr;
        "comp = " ^ layout_comp comp;
      ]

  let print_config config = Pp.printf "%s\n" @@ layout_config config
  let init ~substs rctx curr comp post = C.return { rctx; curr; comp }
  let comp { comp; _ } = comp
  let with_comp comp config = { config with comp }
  let get_rty x { rctx; _ } = RTypectx.get_ty rctx x

  let add_rx rx config =
    { config with rctx = RTypectx.new_to_right config.rctx rx }

  let add_rxs rxs config =
    { config with rctx = RTypectx.new_to_rights config.rctx rxs }

  let reachable { rctx; curr; _ } =
    not @@ Subtyping.sub_srl_bool rctx (curr, EmptyA)

  let abort config =
    if reachable config then Some { config with comp = CErr #: config.comp.ty }
    else None

  let assume phi config =
    if is_true phi then Some config
    else if is_false phi then None
    else
      add_prop_to_rctx phi config.rctx
      |> Option.map @@ fun rctx -> { config with rctx }

  let assert_ phi config =
    let true_branch = assume phi config in
    let false_branch = Option.bind (assume (mk_not phi) config) abort in
    match false_branch with Some _ -> false_branch | None -> true_branch

  let asserts phis config =
    List.fold_left
      (fun acc phi ->
        let^ config = acc in
        assert_ phi config)
      (C.return config) phis

  let admit ~substs sfa config =
    C.return { config with curr = LandA (config.curr, sfa) }

  let append ~substs sfa config =
    C.return { config with curr = SeqA (config.curr, sfa) }

  let reach_bad_state _ = false

  let hatch ~retrty ~sfa_post ({ rctx; curr; comp } as config) =
    match comp.x with
    | CVal _ when not @@ Subtyping.sub_srl_bool rctx (curr, sfa_post) ->
        Some { config with comp = CErr #: comp.ty }
    | CVal v -> (
        match retrty with
        | BaseRty { cty } ->
            let phi = subst_prop (cty.v.x, AC (to_const_ v)) cty.phi in
            Option.bind (assume (mk_not phi) config) abort
        | _ -> None)
    | _ -> Some config

  let output_dot _ = ()

  type iteration_info = unit

  let start_iteration _ = C.fail
  let end_iteration _ = _failatwith __FILE__ __LINE__ "die"

  type witness = { rctx : RTypectx.ctx; curr : sfa }

  let print_witness { rctx; curr } =
    Pp.printf
      "@{bug hatched@}:\nrctx = %s\ncurr = %s\n------------------------\n"
      (RTypectx.layout_typed_l rctx)
      (layout_regex curr)

  let get_witness ({ rctx; curr; comp } as config) =
    match comp.x with CErr -> Some { rctx; curr } | _ -> None
end

module DerivBased (AppendBound : IntT) (EmptyAware : BoolT) (LookAhead : IntT) :
  T = struct
  module EffSFA =
    SFA
      (struct
        let flag = false
      end)
      (struct
        let value = 0
      end)

  module ContSFA =
    SFA
      (struct
        let flag = true
      end)
      (LookAhead)

  type config = {
    rctx : RTypectx.ctx;
    prefix : Tr.trace;
    cont : ContSFA.deriv;
    comp : comp typed;
  }
  (** `rctx` only constrains first-order values *)

  let layout_config { rctx; prefix; cont; comp } =
    String.concat "\n"
      [
        "rctx = " ^ RTypectx.layout_typed_l rctx;
        "prefix = " ^ Tr.layout_trace prefix;
        "cont = " ^ ContSFA.layout_deriv cont;
        "comp = " ^ layout_comp comp;
      ]

  let print_config config = Pp.printf "%s\n" @@ layout_config config
  let comp { comp; _ } = comp
  let with_comp comp config = { config with comp }
  let get_rty x { rctx; _ } = RTypectx.get_ty rctx x

  let add_rx rx config =
    if erase_rty rx.rty = Nt.unit_ty then config
    else { config with rctx = RTypectx.new_to_right config.rctx rx }

  let add_rxs rxs config =
    { config with rctx = RTypectx.new_to_rights config.rctx rxs }

  let n_ = "_n"
  let i_ = "_i"

  let over_reachable { rctx; _ } =
    not @@ Subtyping.is_bot_cty rctx @@ mk_unit_from_prop mk_true

  let reachable { rctx; prefix; _ } =
    not @@ Subtyping.is_bot_cty rctx @@ mk_unit_from_prop @@ smart_and
    @@ Tr.fold
         (function
           | TamperSeal -> Fun.id
           | Atom l -> List.cons @@ L.to_phi l
           | Repeat { from; to_; tr } ->
               List.cons
               @@ Forall
                    ( i_ #: Nt.int_ty,
                      Implies
                        ( And
                            [
                              Lit (mk_geq (AVar i_) from);
                              Lit (mk_lt (AVar i_) to_);
                            ],
                          Tr.fold
                            (function
                              | Atom l -> smart_add_to @@ L.to_phi l
                              | _ -> _failatwith __FILE__ __LINE__ "die")
                            tr mk_true ) ))
         prefix []

  (** CErr if reachable, otherwise safe to prune the path *)
  let abort config =
    if reachable config then Some { config with comp = CErr #: config.comp.ty }
    else None

  let assume phi config =
    if is_true phi then Some config
    else if is_false phi then None
    else
      (* Pp.printf "@{<yellow>assume@} %s\n" @@ layout_prop phi; *)
      add_prop_to_rctx phi config.rctx
      |> Option.map @@ fun rctx -> { config with rctx }

  (** eagerly find assertion failure *)
  let assert_ phi config =
    let true_branch = assume phi config in
    let false_branch = Option.bind (assume (mk_not phi) config) abort in
    match false_branch with Some _ -> false_branch | None -> true_branch

  let asserts phis config =
    List.fold_left
      (fun acc phi ->
        let^ config = acc in
        assert_ phi config)
      (C.return config) phis

  (** find paths in `g` that starts from the initial state of `sfa` and
    ends at a self-accepting state, and augment `config.prefix` with
    it as long as they are compatible

    TODO: alternatively, we may enumerate such paths first
    before matching them with `config.prefix`
 *)
  let admit ~substs sfa config =
    (* Pp.printf "@{<yellow>admitting@} %s\n" @@ layout_regex sfa; *)
    let sfa = List.fold_right (SRL.subst_id << swap) substs sfa in
    let d = EffSFA.init sfa in
    let* _, prefix, d' =
      EffSFA.match_and_refine_trace ~rctx:config.rctx ~substs config.prefix d
    in
    let* () = C.guard @@ EffSFA.is_nullable d' in
    let prefix = List.fold_right Tr.subst_trace_id substs prefix in
    (* Pp.printf "@{<green>admited@} %s\n" @@ Tr.layout_trace prefix; *)
    C.return { config with prefix }

  let append ~substs sfa config =
    let sfa = List.fold_right (SRL.subst_id << swap) substs sfa in
    let d = EffSFA.init sfa in
    let* tr, d' = EffSFA.enum ~substs ~len_range:(0, AppendBound.value) d in
    let* () = C.guard @@ EffSFA.is_nullable d' in
    let tr = List.fold_right Tr.subst_trace_id substs tr in
    let* _, tr', cont =
      ContSFA.match_and_refine_trace ~rctx:config.rctx ~substs tr config.cont
    in
    (* Pp.printf "@{<yellow>append@} %s\n" @@ Tr.layout_trace tr; *)
    C.return { config with prefix = Tr.append config.prefix tr'; cont }

  let init ~substs rctx pre comp post =
    let cont = ContSFA.init post in
    append ~substs pre { rctx; prefix = Tr.empty; cont; comp }

  let reach_bad_state { cont; _ } = EmptyAware.flag && ContSFA.is_empty cont

  (** look for bug and prune terminated good execution
    TODO: create a flag to toggle preemptive bug check
 *)
  let hatch ~retrty ~sfa_post ({ cont; comp; _ } as config) =
    let () =
      Env.show_debug_hatch @@ fun _ ->
      Pp.printf "%s\n-----------------------------\n" @@ layout_config config
    in
    match comp.x with
    | CVal _ when (not @@ ContSFA.is_nullable cont) && reachable config ->
        Some { config with comp = CErr #: comp.ty }
    | CVal (VConst c) ->
        let { v; phi } = rty_to_cty retrty in
        let post = subst_prop (v.x, AC c) phi in
        Option.bind (assume (mk_not post) config) abort
    | CVal (VVar v) when Nt.is_base_tp comp.ty ->
        abort (add_rx v #:: (neg_rty __FILE__ __LINE__ retrty) config)
    | CVal _ -> None (* function value is not checked upon return *)
    | _ when ContSFA.is_empty config.cont && reachable config ->
        Some { config with comp = CErr #: comp.ty }
    | _ -> Some config

  let output_dot name =
    EffSFA.output @@ open_out @@ name ^ "_eff.dot";
    ContSFA.output @@ open_out @@ name ^ "_cont.dot"

  type witness = {
    kind : [ `Preemptive | `Terminated ];
    rctx : RTypectx.ctx;
    prefix : Tr.trace;
  }

  let print_witness { kind; rctx; prefix } =
    Pp.printf
      "@{<bold>%s bug hatched@}:\n\
       rctx = %s\n\
       prefix = %s\n\
       ------------------------\n"
      (match kind with
      | `Preemptive -> "Preemptive"
      | `Terminated -> "Terminated")
      (RTypectx.layout_typed_l rctx)
      (Tr.layout_trace prefix)

  let get_witness ({ rctx; prefix; cont; comp } as config) =
    match comp.x with
    | CErr ->
        if ContSFA.is_empty cont then Some { kind = `Preemptive; rctx; prefix }
        else Some { kind = `Terminated; rctx; prefix }
    | _ -> None

  type iteration_info = {
    lhs_ : string typed;
    fixname_ : string typed;
    letbody_ : comp typed;
    cont_ : ContSFA.deriv;
    prev_rctx : RTypectx.ctx;
    prev_prefix : Tr.trace;
  }

  let rec get_conjuncts phi =
    match phi with
    | Lit lit -> [ lit ]
    | And lits -> List.concat_map get_conjuncts lits
    | _ -> []

  let to_assignment phi (x : string Nt.typed) =
    match x.ty with
    | Ty_bool -> find_boollit_assignment_from_prop_opt phi x.x
    | _ ->
        List.get_opt
        @@ List.filter_map (fun lit -> find_assignment_of_intvar lit x.x)
        @@ get_conjuncts phi

  let[@warning "-8"] start_iteration
      {
        rctx;
        prefix;
        cont;
        comp =
          {
            x =
              CLetE
                {
                  lhs;
                  rhs =
                    {
                      x =
                        CApp
                          {
                            appf =
                              {
                                x = VFix { fixname; fixarg; fixbody };
                                ty = _ty_fix;
                              } as appf;
                            apparg;
                          };
                      ty = _ty_rhs;
                    };
                  letbody;
                };
            ty = _ty_comp;
          };
      } =
    let+ () =
      C.guard
      @@
      match apparg.x with
      | VConst (I 0) -> true
      | VVar x -> (
          let rty = RTypectx.get_ty rctx x in
          let cty = rty_to_cty rty in
          let x, phi = cty_typed_to_prop x #::: cty in
          match to_assignment phi x with
          | Some lit -> equal_lit lit (AC (I 0))
          | None -> false)
      | _ -> false
    in
    let cty =
      Cty.mk_from_prop Nt.int_ty @@ fun { x; ty } ->
      Lit (mk_geq (AVar x) (AC (I 0)))
    in
    let rx = n_ #:: (BaseRty { cty }) in
    let rctx = RTypectx.new_to_right rctx rx in
    let prefix = Tr.snoc TamperSeal prefix in
    let fixbody =
      fixbody
      |> do_subst_comp (fixname.x, appf)
      |> do_subst_comp (fixarg.x, (VVar n_) #: Nt.int_ty)
    in
    let inlined = mk_lete lhs fixbody letbody in
    ( {
        lhs_ = lhs;
        fixname_ = fixname;
        letbody_ = letbody;
        cont_ = cont;
        prev_rctx = rctx;
        prev_prefix = prefix;
      },
      (* TODO: include new construct to `Tr` to avoid tampering of `prefix` *)
      { rctx; prefix; cont; comp = inlined } )

  let end_iteration { lhs_; fixname_; letbody_; cont_; prev_rctx; prev_prefix }
      (config : config) =
    let^ () = C.guard @@ ContSFA.equal_deriv config.cont cont_ in
    let ( let* ) x f = opt_bind x f in
    let ( let+ ) x f = opt_fmap x f in
    let rec remove_trivial_equality phi =
      match phi with
      | And ls -> List.concat_map remove_trivial_equality ls
      | Lit (AAppOp (op, [ l1; l2 ]))
        when Op.id_eq_op op.x && equal_lit l1.x l2.x ->
          []
      | Iff (Lit l1, Lit l2) when equal_lit l1 l2 -> []
      | _ -> [ phi ]
    in
    let rec skolemize ?(phi_i = mk_true) eff = function
      | [] -> Some (phi_i, eff)
      | (x, rty) :: rctx ->
          (* TODO: ignore function binding *)
          let ctys = rty_to_cty rty in
          let x, phi = cty_typed_to_prop x #::: ctys in
          let* lit = to_assignment phi x in
          let phis = remove_trivial_equality @@ subst_prop (x.x, lit) phi in
          let* phi_i =
            List.fold_left
              (fun opt phi ->
                Option.bind opt @@ fun phi_i ->
                let+ () =
                  opt_guard @@ not @@ StrList.exists x.x @@ fv_prop phi
                in
                smart_add_to phi phi_i)
              (Some phi_i) phis
          in
          let eff = Tr.subst_trace (x.x, lit) eff in
          let rctx = RTypectx.subst ~f:subst_rty (x.x, lit) rctx in
          skolemize ~phi_i eff rctx
    in
    let* argvar, comp_after =
      match config.comp.x with
      | CLetE
          {
            lhs;
            rhs =
              {
                x =
                  CApp { appf = { x = VFix { fixname; _ }; _ } as appf; apparg };
                _;
              };
            letbody;
          }
        when fixname.x = fixname_.x && apparg.ty = Nt.int_ty
             && do_subst_comp (lhs.x, (VVar lhs_.x) #: lhs_.ty) letbody
                = letbody_ -> (
          match apparg.x with
          | VVar x ->
              Some (x, mk_lete lhs (mk_app appf (VVar n_) #: Nt.int_ty) letbody)
          | _ -> None)
      | _ -> None
    in
    let* n_plus_one =
      let rty = RTypectx.get_ty config.rctx argvar in
      let cty = rty_to_cty rty in
      let argvar, phi = cty_typed_to_prop argvar #::: cty in
      to_assignment phi argvar
    in
    let* () =
      opt_guard @@ equal_lit n_plus_one @@ mk_plus (AVar n_) (AC (I 1))
    in
    let rctx_i =
      RTypectx.subst ~f:subst_rty (n_, AVar i_)
      @@ applyn ~n:(List.length prev_rctx) List.tl config.rctx
    in
    let* prev_rctx, (_n, rty_n) = List.last_destruct_opt prev_rctx in
    let eff_i =
      Tr.subst_trace (n_, AVar i_)
      @@ Tr.take (Tr.length prev_prefix) config.prefix
    in
    let+ phi_i, eff_i = skolemize eff_i rctx_i in
    let rty =
      join_rty rty_n @@ mk_from_prop Nt.int_ty
      @@ fun n ->
      Forall
        ( i_ #: Nt.int_ty,
          Implies
            ( And
                [
                  Lit (mk_geq (AVar i_) (AC (I 0)));
                  Lit (mk_lt (AVar i_) (AVar n.x));
                ],
              phi_i ) )
    in
    {
      rctx = RTypectx.new_to_right prev_rctx n_ #:: rty;
      prefix =
        Tr.snoc
          (Repeat { from = AC (I 0); to_ = AVar n_; tr = eff_i })
          prev_prefix;
      cont = cont_;
      comp = comp_after;
    }
end
