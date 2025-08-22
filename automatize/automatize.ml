open Sugar
open Language
open Structure
open Rty
open Eff

let rec do_eff rctx =
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
  function
  | Atom Id -> Atom (Trans (Explicit Sft.mk_ident))
  | Atom (Call ev) -> Atom (Call ev)
  | Atom (Trans (Explicit sft)) -> Atom (Trans (Explicit sft))
  | Atom (Trans (Admit srl)) ->
      let sft = Transducize.admit_sft @@ Derivative.from_regex ~is_bot srl in
      Atom (Trans (Explicit sft))
  | Atom (Trans (Append ev)) ->
      let open Sft in
      let init = G.V.create Normal in
      let final = G.V.create Final in
      let loop_edge =
        G.E.create init (Label.Pred (LAlg.mk_top, [ IdentityF ])) init
      in
      let append_edge =
        G.E.create init (T.Label.Epsilon (P.mk_true, [ ev ])) final
      in
      let g = G.add_edge_e (G.add_edge_e G.empty loop_edge) append_edge in
      (* let g = G.add_edge_e G.empty append_edge in *)
      Atom (Trans (Explicit { init; g }))
  | Atom (Trans (Reject pred)) ->
      let open Sft in
      let init = G.V.create Final in
      let keep =
        G.E.create init (T.Label.Pred (LAlg.mk_not pred, [ IdentityF ])) init
      in
      let del = G.E.create init (T.Label.Pred (pred, [])) init in
      let g = G.add_edge_e (G.add_edge_e G.empty keep) del in
      Atom (Trans (Explicit { init; g }))
  | Constrain (eff1, eff2) ->
      let eff1 = do_eff rctx eff1 in
      let eff2 = do_eff rctx eff2 in
      (match eff1 with
      | Atom (Trans (Explicit { init; g })) -> assert (Sft.G.mem_vertex g init)
      | _ -> ());
      Constrain (eff1, eff2)
  | Bind (cx, eff) ->
      let cty = cx.cty in
      let rctx = RTypectx.new_to_right rctx cx.cx #:: (BaseRty { cty }) in
      Bind (cx, do_eff rctx eff)
  | Choice (Seq (Guard phi1, eff1), Seq (Guard phi2, eff2)) -> (
      match (do_eff rctx eff1, do_eff rctx eff2) with
      | Atom (Trans (Explicit sft1)), Atom (Trans (Explicit sft2)) ->
          let sft = Sft.mk_disjunct (phi1, sft1) (phi2, sft2) in
          assert (Sft.G.mem_vertex sft.g sft.init);
          Atom (Trans (Explicit sft))
      | eff1, eff2 -> Choice (Seq (Guard phi1, eff1), Seq (Guard phi2, eff2)))
  | Guard phi -> Guard phi
  | Choice (eff1, eff2) -> Choice (do_eff rctx eff1, do_eff rctx eff2)
  | Seq (eff1, eff2) -> (
      match (do_eff rctx eff1, do_eff rctx eff2) with
      | Atom (Trans (Explicit sft1)), Atom (Trans (Explicit sft2)) ->
          Atom (Trans (Explicit (Sft.mk_compose ~is_bot sft1 sft2)))
      | eff1, eff2 -> Seq (eff1, eff2))

let rec do_rty rctx = function
  | BaseRty cty -> BaseRty cty
  | ArrRty { arr; rethty } ->
      let arr, binding_opt = do_arr rctx arr in
      let rctx =
        match binding_opt with
        | Some binding -> RTypectx.new_to_right rctx binding
        | None -> rctx
      in
      ArrRty { arr; rethty = do_hty rctx rethty }

and do_arr rctx = function
  | NormalArr { rx; rty } ->
      let binding = { rx; rty = do_rty rctx rty } in
      (NormalArr binding, Some binding)
  | GhostArr x -> (GhostArr x, Some x.x #:: (Rty.mk_top x.ty))
  | ArrArr rty -> (ArrArr (do_rty rctx rty), None)

and do_hty rctx = function
  | Rty rty -> Rty (do_rty rctx rty)
  | Monad { ret; eff } ->
      let ret = { ret with rty = do_rty rctx ret.rty } in
      let rctx = RTypectx.new_to_right rctx ret in
      let eff = do_eff rctx eff in
      Monad { ret; eff }
  | Htriple triple -> Htriple triple
  | Inter (h1, h2) -> Inter (do_hty rctx h1, do_hty rctx h2)

let do_ rctx = map_rtys (do_rty rctx)

(* Expose submodules *)
module Regexize = Regexize
