open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.Sft
open Sugar
open Aux

let pprint_pred { events; op_pred } =
  let event_strs = List.map (fun ev -> To_se.pprint (EffEvent ev)) events in
  match op_pred with
  | Whitelist ops_include ->
      let strs = event_strs @ ops_include in
      if List.is_empty strs then "⊥" else String.concat " | " strs
  | Blacklist (phi, ops_exclude) when List.is_empty ops_exclude ->
      _assert __FILE__ __LINE__ "layout_literal: disjointness"
      @@ List.is_empty event_strs;
      To_qualifier.layout phi
  | Blacklist (phi, ops_exclude) ->
      String.concat " | " @@ event_strs
      @ [
          To_qualifier.layout phi ^ "¬(" ^ String.concat " | " ops_exclude ^ ")";
        ]

let pprint_ev { op; args; ret } =
  spf "⟨%s %s = %s⟩" op
    (String.concat " " @@ List.map To_lit.layout_typed_lit args)
    (To_lit.layout_typed_lit ret)

let pprint_func = function IdentityF -> "id" | EventF ev -> pprint_ev ev

let rec pred_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_construct _ -> LAlg.of_sevent @@ To_se.of_ocamlexpr expr
  | Pexp_apply (func, args) -> (
      match (To_expr.id_of_ocamlexpr func, List.map snd args) with
      | "not", [ p ] -> LAlg.mk_not @@ pred_of_ocamlexpr p
      | "&&", [ p1; p2 ] ->
          LAlg.mk_and (pred_of_ocamlexpr p1) (pred_of_ocamlexpr p2)
      | "||", [ p1; p2 ] ->
          LAlg.mk_or (pred_of_ocamlexpr p1) (pred_of_ocamlexpr p2)
      | _ ->
          _failatwith __FILE__ __LINE__
          @@ spf "of_ocamlexpr: %s"
          @@ Pprintast.string_of_expression expr)
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "of_ocamlexpr: %s"
      @@ Pprintast.string_of_expression expr

let ev_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) ->
      let op = String.uncapitalize_ascii @@ To_id.longid_to_id op in
      let args, ret =
        match e.pexp_desc with
        | Pexp_tuple es ->
            Option.get @@ List.last_destruct_opt
            @@ List.map To_lit.typed_lit_of_ocamlexpr es
        | _ -> _failatwith __FILE__ __LINE__ "die"
      in
      { op; args; ret }
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "ev_of_ocamlexpr: %s"
      @@ Pprintast.string_of_expression expr

let func_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_construct (op, None) when String.equal "Id" @@ To_id.longid_to_id op ->
      IdentityF
  | Pexp_construct (op, Some _) -> EventF (ev_of_ocamlexpr expr)
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "of_ocamlexpr: %s"
      @@ Pprintast.string_of_expression expr
