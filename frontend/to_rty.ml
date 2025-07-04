open Ocaml5_parser
open Parsetree

(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar
open Aux
open To_lit
open To_qualifier

let pprint_eff_atom (e : Eff.atom) =
  match e with
  | Call { op; args; ret } ->
      spf "%s ← %s(%s)" (To_lit.layout_typed_lit ret) op
      @@ String.concat ", " (List.map To_lit.layout_typed_lit args)
  | Trans sft -> To_sft.pprint sft

let rec pprint_eff (e : Eff.t) =
  match e with
  | Atom atom -> pprint_eff_atom atom
  | Reach e -> spf "Reach(%s)" @@ pprint_eff e
  | Bind (cx, e) ->
      spf "%s ← %s; %s" cx.cx
        (pprint_parn @@ To_cty.pprint cx.cty)
        (pprint_eff e)
  | Guard phi -> To_qualifier.layout phi
  | Seq (e1, e2) -> spf "%s; %s" (pprint_eff e1) (pprint_eff e2)
  | Choice (e1, e2) -> spf "(%s) | (%s)" (pprint_eff e1) (pprint_eff e2)

let rec eff_of_ocamlexpr expr : Eff.t =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) -> (
      let op = String.uncapitalize_ascii @@ To_id.longid_to_id op in
      match op with
      | "reach" -> Reach (eff_of_ocamlexpr e)
      | "admit" -> Atom (Trans (Admit (To_srl.of_ocamlexpr e)))
      | "reject" -> Atom (Trans (Reject (To_aevent.pred_of_ocamlexpr e)))
      | "append" -> Atom (Trans (Append (To_aevent.ev_of_ocamlexpr e)))
      | _ -> let args, ret =
               match e.pexp_desc with
               | Pexp_tuple es ->
                 Aux.force_last @@ List.map typed_lit_of_ocamlexpr es
               | _ -> _failatwith __FILE__ __LINE__ "die"
        in Atom (Call { op; args; ret })
    )
  | Pexp_sequence (e1, e2) -> Seq (eff_of_ocamlexpr e1, eff_of_ocamlexpr e2)
  | Pexp_assert e -> Guard (qualifier_of_ocamlexpr e)
  | Pexp_let (Asttypes.Nonrecursive, vbs, expr) ->
      let process_vb { pvb_pat; pvb_expr; _ } body : Eff.t =
        let[@warning "-8"] [ { x; ty } ] = To_pat.patten_to_typed_ids pvb_pat in
        let cty = To_cty.of_ocamlexpr pvb_expr in
        Bind ({ cx = x; cty }, body)
      in
      List.fold_right process_vb vbs @@ eff_of_ocamlexpr expr
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "of_ocamlexpr: unsupported expression %s"
      @@ Pprintast.string_of_expression expr

let rec pprint_rty rty =
  match rty with
  | BaseRty { cty } -> pprint_parn (To_cty.pprint cty)
  | ArrRty { arr; rethty } -> spf "%s%s" (pprint_arr arr) (pprint_hty rethty)

and pprint_arr = function
  | NormalArr { rx; rty } -> spf "(%s:%s) → " rx (pprint_rty rty)
  | GhostArr { x; ty } -> spf "(%s:%s) ⇢ " x (Nt.layout ty)
  | ArrArr rty -> spf "%s → " (pprint_rty rty)

and pprint_hty = function
  | Rty rty -> pprint_rty rty
  | Monad { ret; eff } ->
      spf "(%s:%s)!%s" ret.rx (pprint_rty ret.rty) (pprint_eff eff)
  | Htriple { pre; resrty; post } ->
      spf "[%s]%s[%s]" (To_srl.pprint pre) (pprint_rty resrty)
        (To_srl.pprint post)
  | Inter (hty1, hty2) -> spf "%s ⊓ %s" (pprint_hty hty1) (pprint_hty hty2)

(* let hty_of_ocamlexpr expr = *)
(*   let ltlf_hty = To_ltlf_hty.hty_of_ocamlexpr expr in *)
(*   let hty = to_hty ltlf_hty in *)
(*   let hty = normalize_name_hty hty in *)
(*   hty *)

(* let rty_of_ocamlexpr expr = *)
(*   let ltlf_rty = To_ltlf_hty.rty_of_ocamlexpr expr in *)
(*   let rty = to_rty ltlf_rty in *)
(*   let rty = normalize_name_rty rty in *)
(*   rty *)

(* let hty_of_ocamlexpr expr = *)
(*   let ltlf_hty = To_ltlf_hty.hty_of_ocamlexpr expr in *)
(*   let hty = to_hty ltlf_hty in *)
(*   let hty = normalize_name_hty hty in *)
(*   hty *)

(* let rty_of_ocamlexpr expr = *)
(*   let ltlf_rty = To_ltlf_hty.rty_of_ocamlexpr expr in *)
(*   let rty = to_rty ltlf_rty in *)
(*   let rty = normalize_name_rty rty in *)
(*   rty *)

let rec arr_of_ocamlexpr_aux pattern rtyexpr =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  match (get_pat_denoteopt pattern, px, rtyexpr) with
  | None, None, Some rtyexpr -> ArrArr (rty_of_ocamlexpr_aux rtyexpr)
  | None, Some { x = rx; _ }, Some rtyexpr ->
      NormalArr { rx; rty = rty_of_ocamlexpr_aux rtyexpr }
  | Some "ghost", Some { x; ty = Some ty' }, None -> GhostArr Nt.{ x; ty = ty' }
  | _, _, _ -> _failatwith __FILE__ __LINE__ "wrong syntax"

and rty_of_ocamlexpr_aux expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> BaseRty { cty = To_cty.of_ocamlexpr expr }
    | Pexp_fun (_, rtyexpr, pattern, body) ->
        let arr = arr_of_ocamlexpr_aux pattern rtyexpr in
        ArrRty { arr; rethty = hty_of_ocamlexpr_aux body }
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

and hty_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_record ([ (id1, e1); (id2, e2) ], None) -> (
      let id1, id2 = map2 To_id.longid_to_id (id1, id2) in
      let ret = id1 #:: (rty_of_ocamlexpr_aux e1) in
      let eff = eff_of_ocamlexpr e2 in
      match id2 with
      | "eff" -> Monad { ret; eff }
      | _ -> failwith "syntax error")
  | Pexp_record ([ (id1, e1); (id2, e2); (id3, e3) ], None) -> (
      let id1, id2, id3 = map3 To_id.longid_to_id (id1, id2, id3) in
      let pre, post = map2 To_srl.of_ocamlexpr (e1, e3) in
      let resrty = rty_of_ocamlexpr_aux e2 in
      match (id1, id2, id3) with
      | "pre", "res", "post" -> Htriple { pre; resrty; post }
      | "pre", "res", "newadding" ->
          Htriple { pre; resrty; post = SeqA (pre, post) }
      | _ ->
          failwith
            "syntax error: {pre = ...; res = ...; post = ...} or {pre = ...; \
             res = ...; newadding = ...}"
      (* | Pexp_array ls when List.length ls -> *)
      (* failwith "syntax error: empty intersection type" *))
  | Pexp_record (_, _) ->
      failwith
        (spf "syntax error: Hoare Automata Triple %s\n"
           (Pprintast.string_of_expression expr))
  | Pexp_array ls -> (
      let htys = List.map hty_of_ocamlexpr_aux ls in
      match htys with
      | [] -> failwith "syntax error: empty intersection type"
      | hty :: htys -> List.fold_left (fun h1 h2 -> Inter (h1, h2)) hty htys)
  | _ -> Rty (rty_of_ocamlexpr_aux expr)

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  let rty = normalize_name_rty rty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  rty

let hty_of_ocamlexpr expr =
  let hty = hty_of_ocamlexpr_aux expr in
  let hty = normalize_name_hty hty in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  hty

let layout_hty = pprint_hty
let layout_rty = pprint_rty
