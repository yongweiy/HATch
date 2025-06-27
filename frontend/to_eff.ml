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
