open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.LRtyRaw
open Sugar
open Aux

let pprint_eff_atom (e : Eff.atom) =
  match e with
  | Id -> spf "ID"
  | Call { op; args; ret } ->
      spf "%s ← %s(%s)" (To_lit.layout_typed_lit ret) op
      @@ String.concat ", " (List.map To_lit.layout_typed_lit args)
  | Trans (Admit ltlf) -> spf "admit(%s)" (To_ltlf.pprint ltlf)
  | Trans (Reject pred) -> spf "reject(%s)" (To_aevent.pprint_pred pred)
  | Trans (Append ev) -> spf "append(%s)" (To_aevent.pprint_ev ev)
  | Trans (Explicit sft) -> spf "explicit(%s)" (To_sft.pprint sft)

let rec pprint_eff (e : Eff.t) =
  match e with
  | Atom atom -> pprint_eff_atom atom
  | Constrain (e1, e2) ->
      spf "Constrain(%s, %s)" (pprint_eff e1) (pprint_eff e2)
  | Bind (cx, e) ->
      spf "%s ← %s; %s" cx.cx
        (pprint_parn @@ To_cty.pprint cx.cty)
        (pprint_eff e)
  | Guard phi -> To_qualifier.layout phi
  | Seq (e1, e2) -> spf "%s; %s" (pprint_eff e1) (pprint_eff e2)
  | Choice (e1, e2) -> spf "(%s) | (%s)" (pprint_eff e1) (pprint_eff e2)

let rec eff_of_ocamlexpr expr : Eff.t =
  match expr.pexp_desc with
  | Pexp_construct (op, None) when String.equal (To_id.longid_to_id op) "()" ->
      Atom Id
  | Pexp_construct (op, Some e) -> (
      let op = String.uncapitalize_ascii @@ To_id.longid_to_id op in
      match op with
      | "choice" -> (
          match e.pexp_desc with
          | Pexp_tuple [ e1; e2 ] ->
              Choice (eff_of_ocamlexpr e1, eff_of_ocamlexpr e2)
          | _ -> _failatwith __FILE__ __LINE__ "die")
      | "constrain" -> (
          match e.pexp_desc with
          | Pexp_tuple [ e1; e2 ] ->
              Constrain (eff_of_ocamlexpr e1, eff_of_ocamlexpr e2)
          | _ -> _failatwith __FILE__ __LINE__ "die")
      | "guard" -> Guard (To_qualifier.qualifier_of_ocamlexpr e)
      | "admit" -> Atom (Trans (Admit (To_ltlf.of_ocamlexpr e)))
      | "reject" -> Atom (Trans (Reject (To_aevent.pred_of_ocamlexpr e)))
      | "append" -> Atom (Trans (Append (To_aevent.ev_of_ocamlexpr e)))
      | _ ->
          let args, ret =
            match e.pexp_desc with
            | Pexp_tuple es ->
                Aux.force_last @@ List.map To_lit.typed_lit_of_ocamlexpr es
            | _ -> _failatwith __FILE__ __LINE__ "die"
          in
          Atom (Call { op; args; ret }))
  | Pexp_sequence (e1, e2) -> Seq (eff_of_ocamlexpr e1, eff_of_ocamlexpr e2)
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
  | NormalArr { rx; rty } -> spf "(%s:%s)→" rx (pprint_rty rty)
  | GhostArr { x; ty } -> spf "(%s:%s)⇢" x (Nt.layout ty)
  | ArrArr rty -> spf "%s→" (pprint_rty rty)

and pprint_hty = function
  | Rty rty -> pprint_rty rty
  | Monad { ret; eff } ->
      spf "(%s:%s)!%s" ret.rx (pprint_rty ret.rty) (pprint_eff eff)
  | Htriple { pre; resrty; post } ->
      spf "[%s]%s[%s]" (To_ltlf.pprint pre) (pprint_rty resrty)
        (To_ltlf.pprint post)
  | Inter (hty1, hty2) -> spf "%s ⊓ %s" (pprint_hty hty1) (pprint_hty hty2)

(* let get_self ct = *)
(*   let open Nt in *)
(*   match ct.rtyp_desc with *)
(*   | Rtyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty) *)
(*   | _ -> *)
(*       let () = Printf.printf "\nct: %s\n" (layout_coretype ct) in *)
(*       _failatwith __FILE__ __LINE__ "" *)

(* let vars_phi_of_ocamlexpr expr = *)
(*   let rec aux expr = *)
(*     match expr.pexp_desc with *)
(*     | Pexp_constraint (e', ct) -> *)
(*         let v = get_self ct in *)
(*         let vs, phi = aux e' in *)
(*         (v :: vs, phi) *)
(*     | _ -> ([], To_qualifier.qualifier_of_ocamlexpr expr) *)
(*   in *)
(*   let vs, prop = aux expr in *)
(*   (List.rev vs, prop) *)

let rec arr_of_ocamlexpr_aux pattern rtyexpr =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  (* let () = *)
  (*   Printf.printf "get_pat_denoteopt pattern: %s\n" *)
  (*     (match get_pat_denoteopt pattern with None -> "none" | Some x -> x) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "px: %s\n" *)
  (*     (match px with None -> "none" | Some px -> layout_typed (fun x -> x) px) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "rtyexpr: %s\n" *)
  (*     (match rtyexpr with None -> "none" | Some _ -> "some") *)
  (* in *)
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
    (* | Pexp_fun _ -> *)
    (*     _failatwith __FILE__ __LINE__ *)
    (*       (spf "wrong refinement type: %s" *)
    (*          (Pprintast.string_of_expression expr)) *)
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
      let ret = { rx = id1; rty = rty_of_ocamlexpr_aux e1 } in
      let eff = eff_of_ocamlexpr e2 in
      match id2 with
      | "eff" -> Monad { ret; eff }
      | _ -> failwith "syntax error")
  | Pexp_record ([ (id1, e1); (id2, e2); (id3, e3) ], None) -> (
      let id1, id2, id3 = map3 To_id.longid_to_id (id1, id2, id3) in
      let pre, post = map2 To_ltlf.of_ocamlexpr (e1, e3) in
      let resrty = rty_of_ocamlexpr_aux e2 in
      match (id1, id2, id3) with
      | "pre", "res", "post" -> Htriple { pre; resrty; post }
      | "pre", "res", "newadding" ->
          Htriple { pre; resrty; post = SeqL (pre, post) }
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
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  rty

let hty_of_ocamlexpr expr =
  let hty = hty_of_ocamlexpr_aux expr in
  (* let () = Printf.printf "ZZ: %s\n" (pprint_hty rty) in *)
  hty

let layout_hty = pprint_hty
let layout_rty = pprint_rty
