open Sugar
open Language
open Rty

let mk_simp_pred rctx =
  let is_bot = Subtyping.is_bot_cty rctx << Cty.mk_unit_from_prop in
  simp_opt ~is_bot

let extend_rctx_with_cxs rctx cxs =
  RTypectx.new_to_rights rctx
  @@ List.map (fun cx -> { rx = cx.cx; rty = BaseRty { cty = cx.cty } }) cxs

let[@warning "-8"] is_reachable (SftT (_, sft)) = SFT.is_reachable sft
let[@warning "-8"] display (SftT (_, sft)) = SFT.display layout_label sft

let to_sft ~rctx =
  let rec aux = function
    | StarT (AtomT (p, fns)) -> ([], mk_star_atom p fns)
    | AtomT (p, fns) ->
      Printf.printf "AtomT %s\n" @@ layout_label (p, fns);
      ([], mk_atom p fns)
    | StarT t -> failwith "UNIMP: StarT only supported on AtomT"
    | ConcatT (t1, t2) ->
        let ctx1, sft1 = aux t1 in
        SFT.display layout_label sft1;
        let ctx2, sft2 = aux t2 in
        SFT.display layout_label sft2;
        (ctx1 @ ctx2, SFT.mk_concat sft1 sft2)
    | UnionT (t1, t2) ->
        let ctx1, sft1 = aux t1 in
        let ctx2, sft2 = aux t2 in
        (ctx1 @ ctx2, SFT.mk_union sft1 sft2)
    | ComposeT (t1, t2) ->
        let ctx1, sft1 = aux t1 in
        let ctx2, sft2 = aux t2 in
        let ctx = ctx1 @ ctx2 in
        let simp_pred = mk_simp_pred @@ extend_rctx_with_cxs rctx ctx in
        (ctx, SFT.mk_compose ~simp_pred sft1 sft2)
    | ExT (x, t) ->
        let ctx, sft = aux t in
        (x :: ctx, sft)
    | SftT (ctx, sft) -> (ctx, sft)
  in
  aux

let to_sfa =
  let rec aux = function
    | AtomL p -> ([], mk_atom p [])
    | StarL (AtomL p) -> ([], mk_star_atom p [])
    | StarL l -> failwith "UNIMP: StarL only supported on AtomL"
    | ConcatL (l1, l2) ->
        let ctx1, sfa1 = aux l1 in
        let ctx2, sfa2 = aux l2 in
        (ctx1 @ ctx2, SFT.mk_concat sfa1 sfa2)
    | UnionL (l1, l2) ->
        let ctx1, sfa1 = aux l1 in
        let ctx2, sfa2 = aux l2 in
        (ctx1 @ ctx2, SFT.mk_union sfa1 sfa2)
    | InvImgL (srt, l) -> failwith "InvImgL not supported"
    | ExL (x, l) ->
        let ctx, sfa = aux l in
        (x :: ctx, sfa)
    | SfaL (ctx, sfa) -> (ctx, sfa)
  in
  aux

let mk_ident = SftT ([], mk_ident)
let mk_any = SfaL ([], mk_any)

(* TODO: we should attempt to simply ctx when perform compositions *)

let mk_union ~rctx srt1 srt2 =
  let ctx1, sft1 = to_sft ~rctx srt1 in
  let ctx2, sft2 = to_sft ~rctx srt2 in
  SftT (ctx1 @ ctx2, SFT.mk_union sft1 sft2)

let mk_compose ~rctx srt1 srt2 =
  let ctx1, sft1 = to_sft ~rctx srt1 in
  let ctx2, sft2 = to_sft ~rctx srt2 in
  let ctx = ctx1 @ ctx2 in
  let simp_pred = mk_simp_pred @@ extend_rctx_with_cxs rctx ctx in
  SftT (ctx1 @ ctx2, SFT.mk_compose ~simp_pred sft1 sft2)

let restrict_domain ~rctx srt srl =
  let ctx1, sft = to_sft ~rctx srt in
  let ctx2, sfa = to_sfa srl in
  SFT.display layout_label sft;
  let ctx = ctx1 @ ctx2 in
  let is_bot = Subtyping.is_bot_cty (extend_rctx_with_cxs rctx ctx) << Cty.mk_unit_from_prop in
  SftT (ctx1 @ ctx2, SFT.restrict_domain ~is_bot sft sfa)

let mk_ran ~rctx srt =
  let ctx, sft = to_sft ~rctx srt in
  let simp_pred = mk_simp_pred @@ extend_rctx_with_cxs rctx ctx in
  SfaL (ctx, SFT.mk_ran sft)
