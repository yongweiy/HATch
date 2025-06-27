open Language
module Typectx = NTypectx

(* open Zzdatatype.Datatype *)
open Sugar

(* open Qualifiercheck *)
open RtyRaw
(* open Aux *)

let rec hty_check opctx ctx (hty : hty) : hty =
  let () =
    MetaConfig.show_log "ntyping" @@ fun _ ->
    Printf.printf ">>>>>>>>>>>>Hty Check %s\n" (To_rty.layout_hty hty)
  in
  match hty with
  | Rty rty -> Rty (rty_check opctx ctx rty)
  | Monad { ret; eff } ->
      let ret = { ret with rty = rty_check opctx ctx ret.rty } in
      let ctx' =
        Typectx.new_to_right ctx Nt.{ x = ret.rx; ty = erase_rty ret.rty }
      in
      let eff = eff_check opctx ctx' eff in
      Monad { ret; eff }
  | Htriple { pre; resrty; post } ->
      let pre = Srlcheck.check opctx ctx pre in
      let post = Srlcheck.check opctx ctx post in
      let resrty = rty_check opctx ctx resrty in
      Htriple { pre; resrty; post }
  | Inter (h1, h2) ->
      let h1 = hty_check opctx ctx h1 in
      let h2 = hty_check opctx ctx h2 in
      let _ =
        _assert __FILE__ __LINE__ "syntax error: intersection type"
          (Nt.eq (erase_hty h1) (erase_hty h2))
      in
      Inter (h1, h2)

and trans_check opctx ctx : RtyRaw.Trans.t -> Trans.t = function
  | Explicit sft -> _failatwith __FILE__ __LINE__ "UNIMP"
  | Admit sfa -> Admit (Srlcheck.check opctx ctx sfa)
  | Append ev -> Append (Aeventcheck.check_ev opctx ctx ev)
  | Reject pred -> Reject (Aeventcheck.check_pred opctx ctx pred)

and eff_check opctx ctx = function
  | Atom atom -> Atom (eff_atom_check opctx ctx atom)
  | Reach eff -> Reach (eff_check opctx ctx eff)
  | Bind (ctyped, eff) ->
      let ctyped = { ctyped with cty = Ctycheck.check opctx ctx ctyped.cty } in
      let ctx' =
        Typectx.new_to_right ctx Nt.{ x = ctyped.cx; ty = Cty.erase ctyped.cty }
      in
      Bind (ctyped, eff_check opctx ctx' eff)
  | Guard prop -> Guard (Qualifiercheck.type_check_qualifier opctx ctx prop)
  | Seq (eff1, eff2) -> Seq (eff_check opctx ctx eff1, eff_check opctx ctx eff2)
  | Choice (eff1, eff2) -> Choice (eff_check opctx ctx eff1, eff_check opctx ctx eff2)

and eff_atom_check opctx ctx = function
  | Call ev -> Call (Aeventcheck.check_ev opctx ctx ev)
  | Trans trans -> Trans (trans_check opctx ctx trans)

and arr_check opctx ctx (arr : arr) : arr * string Nt.typed option =
  match arr with
  | NormalArr { rx; rty } ->
      let rty = rty_check opctx ctx rty in
      (NormalArr { rx; rty }, Some Nt.{ x = rx; ty = erase_rty rty })
  | GhostArr x -> (GhostArr x, Some x)
  | ArrArr rty -> (ArrArr (rty_check opctx ctx rty), None)

and rty_check opctx ctx (hty : rty) : rty =
  let () =
    MetaConfig.show_log "ntyping" @@ fun _ ->
    Printf.printf ">>>>>>>>>>>>Rty Check %s\n" (To_rty.layout_rty hty)
  in
  match hty with
  | BaseRty { cty } -> BaseRty { cty = Ctycheck.check opctx ctx cty }
  | ArrRty { arr; rethty } ->
      let arr, binding = arr_check opctx ctx arr in
      let ctx' =
        match binding with
        | None -> ctx
        | Some binding -> Typectx.new_to_right ctx binding
      in
      let rethty = hty_check opctx ctx' rethty in
      ArrRty { arr; rethty }
