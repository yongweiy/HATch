open Syntax
module Raw = RtyRaw
open Rty
module Cty = Coersion_cty
module A = Coersion_aevent

let rec force = function
  | Raw.AtomT (p, fns) -> AtomT (A.force_pred p, List.map A.force_func fns)
  | Raw.StarT srt -> StarT (force srt)
  | Raw.ConcatT (srt1, srt2) -> ConcatT (force srt1, force srt2)
  | Raw.UnionT (srt1, srt2) -> UnionT (force srt1, force srt2)
  | Raw.ComposeT (srt1, srt2) -> ComposeT (force srt1, force srt2)
  | Raw.ExT (cx, srt) -> ExT ({ cx = cx.cx; cty = Cty.force cx.cty }, force srt)
  | Raw.SftT _ -> failwith "force: SftT not supported"

let rec besome = function
  | AtomT (p, fns) -> Raw.AtomT (A.besome_pred p, List.map A.besome_func fns)
  | StarT srt -> Raw.StarT (besome srt)
  | ConcatT (srt1, srt2) -> Raw.ConcatT (besome srt1, besome srt2)
  | UnionT (srt1, srt2) -> Raw.UnionT (besome srt1, besome srt2)
  | ComposeT (srt1, srt2) -> Raw.ComposeT (besome srt1, besome srt2)
  | ExT (cx, srt) ->
      let cty = Cty.besome cx.cty in
      Raw.ExT ({ cx = cx.cx; cty }, besome srt)
  | SftT _ -> failwith "besome: SftT not supported"

let rec force_srl = function
  | Raw.AtomL p -> AtomL (A.force_pred p)
  | Raw.StarL srl -> StarL (force_srl srl)
  | Raw.ConcatL (srl1, srl2) -> ConcatL (force_srl srl1, force_srl srl2)
  | Raw.UnionL (srl1, srl2) -> UnionL (force_srl srl1, force_srl srl2)
  | Raw.InvImgL (srt, srl) -> InvImgL (force srt, force_srl srl)
  | Raw.ExL (cx, srl) ->
      ExL ({ cx = cx.cx; cty = Cty.force cx.cty }, force_srl srl)
  | Raw.SfaL _ -> failwith "force_srl: SfaL not supported"

let rec besome_srl = function
  | AtomL p -> Raw.AtomL (A.besome_pred p)
  | StarL srl -> Raw.StarL (besome_srl srl)
  | ConcatL (srl1, srl2) -> Raw.ConcatL (besome_srl srl1, besome_srl srl2)
  | UnionL (srl1, srl2) -> Raw.UnionL (besome_srl srl1, besome_srl srl2)
  | InvImgL (srt, srl) -> Raw.InvImgL (besome srt, besome_srl srl)
  | ExL (cx, srl) ->
      Raw.ExL ({ cx = cx.cx; cty = Cty.besome cx.cty }, besome_srl srl)
  | SfaL _ -> failwith "besome_srl: SfaL not supported"
