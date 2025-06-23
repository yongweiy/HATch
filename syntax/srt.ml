module F (L : Lit.T) = struct
  open Sexplib.Std
  open Sugar
  module Cty = Cty.F (L)
  open Cty
  module SFT = Sft.F (L)
  include SFT

  (** Symbolic Regular Transducer *)
  type srt =
    | AtomT of pred * func list
    | StarT of srt
    | ConcatT of srt * srt
    | UnionT of srt * srt
    | ComposeT of srt * srt
    | ExT of string ctyped * srt
    | SftT of string ctyped list * sft
  [@@deriving sexp]

  (** Symbolic Regular Language *)
  type srl =
    | AtomL of pred
    | StarL of srl
    | ConcatL of srl * srl
    | UnionL of srl * srl
    | InvImgL of srt * srl
    | ExL of string ctyped * srl
    | SfaL of string ctyped list * sft
  [@@deriving sexp]

  let subst_srt ((y, z) as yz) srt =
    let rec aux = function
      | AtomT (p, fns) -> AtomT (subst_pred yz p, List.map (subst_func yz) fns)
      | StarT t -> StarT (aux t)
      | ConcatT (t1, t2) -> ConcatT (aux t1, aux t2)
      | UnionT (t1, t2) -> UnionT (aux t1, aux t2)
      | ComposeT (t1, t2) -> ComposeT (aux t1, aux t2)
      | ExT (cx, t) ->
          ExT
            ( { cx with cty = subst yz cx.cty },
              if String.equal y cx.cx then t else aux t )
      | SftT (cxs, sft) ->
          let flag, cxs =
            List.fold_left_map
              (fun flag cx ->
                ( flag && (not @@ String.equal y cx.cx),
                  if flag then { cx with cty = subst yz cx.cty } else cx ))
              true cxs
          in
          SftT (cxs, if flag then SFT.subst_sft yz sft else sft)
    in
    aux srt

  let subst_srl ((y, z) as yz) srl =
    let rec aux = function
      | AtomL p -> AtomL (subst_pred yz p)
      | StarL l -> StarL (aux l)
      | ConcatL (l1, l2) -> ConcatL (aux l1, aux l2)
      | UnionL (l1, l2) -> UnionL (aux l1, aux l2)
      | InvImgL (srt, l) -> InvImgL (subst_srt yz srt, aux l)
      | ExL (cx, l) ->
          ExL
            ( { cx with cty = subst yz cx.cty },
              if String.equal y cx.cx then l else aux l )
      | SfaL (cxs, sfa) ->
          let flag, cxs =
            List.fold_left_map
              (fun flag cx ->
                ( flag && (not @@ String.equal y cx.cx),
                  if flag then { cx with cty = subst yz cx.cty } else cx ))
              true cxs
          in
          SfaL (cxs, if flag then SFT.subst_sft yz sfa else sfa)
    in
    aux srl

  let rec fv_srt = function
    | AtomT (pred, fns) -> fv_pred pred @ List.concat_map fv_func fns
    | StarT t -> fv_srt t
    | ConcatT (t1, t2) -> fv_srt t1 @ fv_srt t2
    | UnionT (t1, t2) -> fv_srt t1 @ fv_srt t2
    | ComposeT (t1, t2) -> fv_srt t1 @ fv_srt t2
    | ExT (cx, t) ->
        fv cx.cty @ List.filter (not << String.equal cx.cx) (fv_srt t)
    | SftT (cxs, sft) ->
        List.fold_right
          (fun cx acc ->
            fv cx.cty @ List.filter (not << String.equal cx.cx) acc)
          cxs (fv_sft sft)

  let rec fv_srl = function
    | AtomL pred -> fv_pred pred
    | StarL l -> fv_srl l
    | ConcatL (l1, l2) -> fv_srl l1 @ fv_srl l2
    | UnionL (l1, l2) -> fv_srl l1 @ fv_srl l2
    | InvImgL (srt, l) -> fv_srt srt @ fv_srl l
    | ExL (cx, l) ->
        fv cx.cty @ List.filter (not << String.equal cx.cx) (fv_srl l)
    | SfaL (cxs, sfa) ->
        List.fold_right
          (fun cx acc ->
            fv cx.cty @ List.filter (not << String.equal cx.cx) acc)
          cxs (fv_sft sfa)

  let rec normalize_name_srt = function
    | AtomT (p, fns) -> AtomT (normalize_name_pred p, fns)
    | StarT t -> StarT (normalize_name_srt t)
    | ConcatT (t1, t2) -> ConcatT (normalize_name_srt t1, normalize_name_srt t2)
    | UnionT (t1, t2) -> UnionT (normalize_name_srt t1, normalize_name_srt t2)
    | ComposeT (t1, t2) ->
        ComposeT (normalize_name_srt t1, normalize_name_srt t2)
    | ExT (cx, t) ->
        ExT ({ cx with cty = Cty.normalize_name cx.cty }, normalize_name_srt t)
    | SftT (cxs, sft) ->
        SftT
          ( List.map (fun cx -> { cx with cty = Cty.normalize_name cx.cty }) cxs,
            SFT.normalize_name sft )

  let rec normalize_name_srl = function
    | AtomL p -> AtomL (normalize_name_pred p)
    | StarL l -> StarL (normalize_name_srl l)
    | ConcatL (l1, l2) -> ConcatL (normalize_name_srl l1, normalize_name_srl l2)
    | UnionL (l1, l2) -> UnionL (normalize_name_srl l1, normalize_name_srl l2)
    | InvImgL (srt, l) -> InvImgL (normalize_name_srt srt, normalize_name_srl l)
    | ExL (cx, l) ->
        ExL ({ cx with cty = Cty.normalize_name cx.cty }, normalize_name_srl l)
    | SfaL (cxs, sfa) ->
        SfaL
          ( List.map (fun cx -> { cx with cty = Cty.normalize_name cx.cty }) cxs,
            SFT.normalize_name sfa )
end
