open Ocaml5_parser
open Parsetree

(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar
open Aux
open To_qualifier
open To_lit

let pprint_eff_atom (e : Eff.eff_atom) =
  match e with
  | ECall { op; args; ret } ->
      spf "%s ← %s(%s)" (To_lit.layout_typed_lit ret) op
      @@ String.concat ", " (List.map To_lit.layout_typed_lit args)
  | ETrans sft -> To_sft.pprint sft

let rec pprint_eff (e : Eff.eff) =
  match e with
  | EAtom atom -> pprint_eff_atom atom
  | EReach e -> spf "Reach(%s)" @@ pprint_eff e
  | EBind (cx, e) ->
      spf "%s ← %s; %s" cx.cx
        (pprint_parn @@ To_cty.pprint cx.cty)
        (pprint_eff e)
  | EGuard phi -> To_qualifier.layout phi
  | ESeq (e1, e2) -> spf "%s; %s" (pprint_eff e1) (pprint_eff e2)
  | EChoice (e1, e2) -> spf "(%s) | (%s)" (pprint_eff e1) (pprint_eff e2)

let rec eff_of_ocamlexpr expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) -> (
      let op = String.uncapitalize_ascii @@ To_id.longid_to_id op in
      match op with
      | "reach" -> EReach (eff_of_ocamlexpr e)
      | _ -> let args, ret =
               match e.pexp_desc with
               | Pexp_tuple es ->
                 Aux.force_last @@ List.map typed_lit_of_ocamlexpr es
               | _ -> _failatwith __FILE__ __LINE__ "die"
        in EAtom (ECall { op; args; ret })
    )
  | Pexp_sequence (e1, e2) -> ESeq (eff_of_ocamlexpr e1, eff_of_ocamlexpr e2)
  | Pexp_assert e -> EGuard (qualifier_of_ocamlexpr e)
  | Pexp_let (Asttypes.Nonrecursive, vbs, expr) ->
      let process_vb { pvb_pat; pvb_expr; _ } body =
        let[@warning "-8"] [ { x; ty } ] = To_pat.patten_to_typed_ids pvb_pat in
        let cty = To_cty.of_ocamlexpr pvb_expr in
        EBind ({ cx = x; cty }, body)
      in
      List.fold_right process_vb vbs @@ eff_of_ocamlexpr expr
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "of_ocamlexpr: unsupported expression %s"
      @@ Pprintast.string_of_expression expr
