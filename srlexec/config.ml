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
    string rtyped list ->
    sfa ->
    comp typed ->
    sfa ->
    config C.t

  val comp : config -> comp typed
  val with_comp : comp typed -> config -> config
  val add_rx : string rtyped -> config -> config
  val add_rxs : string rtyped list -> config -> config
  val abort : config -> config option
  val assume : prop -> config -> config option
  val assert_ : prop -> config -> config option
  val asserts : prop list -> config -> config C.t
  val admit : substs:(string * string) list -> sfa -> config -> config C.t
  val append : substs:(string * string) list -> sfa -> config -> config C.t
  val hatch : retrty:rty -> sfa_post:sfa -> config -> config option

  type witness

  val layout_witness : witness -> string
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

  let init ~substs rxs curr comp post =
    C.return { rctx = RTypectx.of_rxs rxs; curr; comp }

  let comp { comp; _ } = comp
  let with_comp comp config = { config with comp }

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

  type witness = { rctx : RTypectx.ctx; curr : sfa }

  let layout_witness { rctx; curr } =
    Printf.sprintf "bug hatched:\nrctx = %s\ncurr = %s"
      (RTypectx.layout_typed_l rctx)
      (layout_regex curr)

  let print_witness witness = Pp.printf "%s\n" @@ layout_witness witness

  let get_witness ({ rctx; curr; comp } as config) =
    match comp.x with CErr -> Some { rctx; curr } | _ -> None
end

module DerivBased : T = struct
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

  let add_rx rx config =
    { config with rctx = RTypectx.new_to_right config.rctx rx }

  let add_rxs rxs config =
    { config with rctx = RTypectx.new_to_rights config.rctx rxs }

  let over_reachable { rctx; _ } =
    not @@ Subtyping.is_bot_cty rctx @@ mk_unit_from_prop mk_true

  let reachable { rctx; prefix; _ } =
    let rxs =
      Tr.fold_lefti (fun index rxs l -> rxs @ L.to_rxs ~index l) [] prefix
    in
    let rctx' = RTypectx.new_to_rights rctx rxs in
    not @@ Subtyping.is_bot_cty rctx' @@ mk_unit_from_prop mk_true

  (** CErr if reachable, otherwise safe to prune the path *)
  let abort config =
    if reachable config then Some { config with comp = CErr #: config.comp.ty }
    else None

  let assume phi config =
    if is_true phi then Some config
    else if is_false phi then None
    else
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
    let* prefix, d' =
      EffSFA.match_and_refine_trace ~rctx:config.rctx ~substs config.prefix d
    in
    let* () = C.guard @@ EffSFA.is_nullable d' in
    let prefix = List.fold_right Tr.subst_id substs prefix in
    (* Pp.printf "@{<green>admited@} %s\n" @@ Tr.layout_trace prefix; *)
    C.return { config with prefix }

  let append ~substs sfa config =
    let sfa = List.fold_right (SRL.subst_id << swap) substs sfa in
    let d = EffSFA.init sfa in
    let* tr, d' =
      EffSFA.enum ~substs ~len_range:(0, Env.get_exec_max_pre_length ()) d
    in
    let* () = C.guard @@ EffSFA.is_nullable d' in
    let tr = List.fold_right Tr.subst_id substs tr in
    let* tr', cont =
      ContSFA.match_and_refine_trace ~rctx:config.rctx ~substs tr config.cont
    in
    (* Pp.printf "@{<yellow>append@} %s\n" @@ Tr.layout_trace tr; *)
    C.return { config with prefix = Tr.append config.prefix tr'; cont }

  let init ~substs rxs pre comp post =
    let cont = ContSFA.init post in
    append ~substs pre
      { rctx = RTypectx.of_rxs rxs; prefix = Tr.empty; cont; comp }

  (** look for bug and prune terminated good execution
    TODO: create a flag to toggle preemptive bug check
 *)
  let hatch ~retrty ~sfa_post ({ cont; comp; _ } as config) =
    Pp.printf "@{<yellow>hatch:@}\n%s\n-----------------------------\n"
    @@ layout_config config;
    match comp.x with
    | CVal _ when (not @@ ContSFA.is_nullable cont) && reachable config ->
        Some { config with comp = CErr #: comp.ty }
    | CVal v -> (
        match retrty with
        | BaseRty { cty } ->
            let phi = subst_prop (cty.v.x, AC (to_const_ v)) cty.phi in
            Option.bind (assume (mk_not phi) config) abort
        | _ -> None (* function value is not checked upon return *))
    | _ when ContSFA.is_empty config.cont && reachable config ->
        Some { config with comp = CErr #: comp.ty }
    | _ -> Some config

  type witness = {
    kind : [ `Preemptive | `Terminated ];
    rctx : RTypectx.ctx;
    prefix : Tr.trace;
  }

  let layout_witness { kind; rctx; prefix } =
    Printf.sprintf "%s bug hatched:\nrctx = %s\nprefix = %s"
      (match kind with
      | `Preemptive -> "Preemptive"
      | `Terminated -> "Terminated")
      (RTypectx.layout_typed_l rctx)
      (Tr.layout_trace prefix)

  let print_witness witness = Pp.printf "%s\n" @@ layout_witness witness

  let get_witness ({ rctx; prefix; cont; comp } as config) =
    match comp.x with
    | CErr ->
        if ContSFA.is_empty cont then Some { kind = `Preemptive; rctx; prefix }
        else Some { kind = `Terminated; rctx; prefix }
    | _ -> None
end
