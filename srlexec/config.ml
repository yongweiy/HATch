open Language
open TypedCoreEff
open Rty
open Sugar
open Utils
module C = Choice
module D = Deriv
module L = Literal
module Tr = Trace

type config = {
  rctx : RTypectx.ctx;
  prefix : Tr.trace;
  cont : sfa;
  comp : comp typed;
}
(** `rctx` only constrains first-order values *)

let with_comp comp config = { config with comp }

let layout_config { rctx; prefix; cont; comp } =
  String.concat "\n"
    [
      "rctx = " ^ RTypectx.layout_typed_l rctx;
      "prefix = " ^ Tr.layout_trace prefix;
      "cont = " ^ layout_regex cont;
      "comp = " ^ layout_comp comp;
    ]

let print_config config = Pp.printf "%s\n" @@ layout_config config

let over_reachable { rctx; _ } =
  not @@ Subtyping.is_bot_cty rctx @@ mk_unit_from_prop mk_true

let reachable { rctx; prefix; _ } =
  let rxs =
    Tr.fold_lefti (fun index rxs l -> rxs @ L.to_rxs ~index l) [] prefix
  in
  let rctx' = RTypectx.new_to_rights rctx rxs in
  not @@ Subtyping.is_bot_cty rctx' @@ mk_unit_from_prop mk_true

let add_rx rx config =
  { config with rctx = RTypectx.new_to_right config.rctx rx }

let add_rxs rxs config =
  { config with rctx = RTypectx.new_to_rights config.rctx rxs }

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

(** eagerly find assertion failure
   TODO: try swap the order of two branches *)
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
  let sfa = List.fold_right (SRL.subst_id << swap) substs sfa in
  D.G.init sfa;
  let* prefix, sfa' =
    D.match_and_refine_trace ~rctx:config.rctx ~substs config.prefix sfa
  in
  let* () = C.guard @@ D.is_nullable sfa' in
  let prefix = List.fold_right Tr.subst_id substs prefix in
  (* Pp.printf "@{<yellow>admit@} %s\n" @@ Tr.layout_trace prefix; *)
  C.return { config with prefix }

let append ~substs sfa config =
  let sfa = List.fold_right (SRL.subst_id << swap) substs sfa in
  D.G.init sfa;
  let* tr, sfa' =
    D.enum ~rctx:config.rctx ~substs
      ~len_range:(0, Env.get_exec_max_pre_length ())
      sfa
  in
  let* () = C.guard @@ D.is_nullable sfa' in
  let tr = List.fold_right Tr.subst_id substs tr in
  (* Pp.printf "@{<yellow>append@} %s\n" @@ Tr.layout_trace tr; *)
  let* tr', cont =
    D.match_and_refine_trace ~rctx:config.rctx ~substs tr config.cont
  in
  C.return { config with prefix = Tr.append config.prefix tr'; cont }

let init rxs pre comp post =
  D.G.init post;
  append pre
    { rctx = RTypectx.of_rxs rxs; prefix = Tr.empty; cont = post; comp }

(** look for bug and prune terminated good execution
    TODO: create a flag to toggle preemptive bug check
 *)
let hatch ~retrty ({ cont; comp; _ } as config) =
  match comp.x with
  | CVal _ when (not @@ D.is_nullable cont) && reachable config ->
      Some { config with comp = CErr #: comp.ty }
  | CVal v -> (
      match retrty with
      | BaseRty { cty } ->
          let phi = subst_prop (cty.v.x, AC (to_const_ v)) cty.phi in
          Option.bind (assume (mk_not phi) config) abort
      | _ -> None (* function value is not checked upon return *))
  | _ when SRL.is_empty config.cont && reachable config ->
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
      if SRL.is_empty cont then Some { kind = `Preemptive; rctx; prefix }
      else Some { kind = `Terminated; rctx; prefix }
  | _ -> None
