module F (L : Lit.T) = struct
  (* open Sexplib.Std *)
  module LTLf = Ltlf.F (L)
  module SRT = Srt.F (L)
  module LRty = Rty_tree.SyntaxF (LTLf) (SRT) (L)
  module SRL = LTLf.SRL
  module RRty = Rty_tree.SyntaxF (SRL) (SRT) (L)
  include SRL
  include SRT
  include RRty

  let rec apply_pred_rty pred rty =
    let open LRty in
    match rty with
    | BaseRty _ -> rty
    | ArrRty { arr; rethty } ->
        ArrRty
          { arr = apply_pred_arr pred arr; rethty = apply_pred_hty pred rethty }

  and apply_pred_arr pred arr =
    let open LRty in
    match arr with
    | NormalArr { rx; rty } -> NormalArr { rx; rty = apply_pred_rty pred rty }
    | GhostArr _ -> arr
    | ArrArr rty -> ArrArr (apply_pred_rty pred rty)

  and apply_pred_hty pred hty =
    let open LRty in
    match hty with
    | Rty rty -> Rty (apply_pred_rty pred rty)
    | TMonad _ -> hty
    | Htriple { pre; resrty; post } ->
        Htriple
          {
            pre = LTLf.apply_pred pred pre;
            resrty = apply_pred_rty pred resrty;
            post = LTLf.apply_pred pred post;
          }
    | Inter (hty1, hty2) ->
        Inter (apply_pred_hty pred hty1, apply_pred_hty pred hty2)

  let rec to_hty = function
    | LRty.Rty rty -> Rty (to_rty rty)
    | LRty.TMonad { retrty; trans } ->
        TMonad { retrty = to_rty retrty; trans = to_trans trans }
    | LRty.Htriple { pre; resrty; post } ->
        Htriple
          {
            pre = LTLf.to_srl pre;
            resrty = to_rty resrty;
            post = LTLf.to_srl post;
          }
    | LRty.Inter (hty1, hty2) -> Inter (to_hty hty1, to_hty hty2)

  and to_trans = function
    | LRty.PreAndPost (pre, post) -> PreAndPost (pre, post)
    | LRty.PreToPost srt -> PreToPost srt

  and to_arr = function
    | LRty.NormalArr { rx; rty } -> NormalArr { rx; rty = to_rty rty }
    | LRty.GhostArr x -> GhostArr x
    | LRty.ArrArr rty -> ArrArr (to_rty rty)

  and to_rty = function
    | LRty.BaseRty { cty } -> BaseRty { cty }
    | LRty.ArrRty { arr; rethty } ->
        ArrRty { arr = to_arr arr; rethty = to_hty rethty }

  (* normalize name *)

  let rec normalize_name_rty tau1 =
    match tau1 with
    | BaseRty { cty } -> BaseRty { cty = Cty.normalize_name cty }
    | ArrRty { arr; rethty } ->
        ArrRty
          { arr = normalize_name_arr arr; rethty = normalize_name_hty rethty }

  and normalize_name_arr = function
    | NormalArr { rx; rty } -> NormalArr { rx; rty = normalize_name_rty rty }
    | GhostArr Nt.{ x; ty } -> GhostArr Nt.{ x; ty }
    | ArrArr rty -> ArrArr (normalize_name_rty rty)

  and normalize_name_hty tau =
    match tau with
    | Rty rty -> Rty (normalize_name_rty rty)
    | TMonad { retrty; trans } ->
        TMonad { retrty = normalize_name_rty retrty; trans }
    | Htriple { pre; resrty; post } ->
        Htriple { pre; resrty = normalize_name_rty resrty; post }
    | Inter (hty1, hty2) ->
        let hty1 = normalize_name_hty hty1 in
        let hty2 = normalize_name_hty hty2 in
        Inter (hty1, hty2)
end
