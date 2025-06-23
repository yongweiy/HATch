open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.SRT
open Sugar
open Aux

let rec pprint = function
  | AtomT (p, fns) ->
      spf "%s/[%s]" (To_aevent.pprint_pred p)
        (List.to_string To_aevent.pprint_func fns)
  | ConcatT (t1, t2) -> spf "(%s;%s)" (pprint t1) (pprint t2)
  | StarT t -> spf "(%s)*" (pprint t)
  | UnionT (t1, t2) -> spf "(%s|%s)" (pprint t1) (pprint t2)
  | ComposeT (t1, t2) -> spf "(%s∘%s)" (pprint t1) (pprint t2)
  | ExT (cx, t) ->
      spf "∃%s:%s.%s" cx.cx (pprint_parn @@ To_cty.layout cx.cty) (pprint t)
  | SftT _ -> _failatwith __FILE__ __LINE__ "TODO: pprint SftT"

let layout = pprint

let of_ocamlexpr_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_apply (func, args) -> (
        match (To_expr.id_of_ocamlexpr func, List.map snd args) with
        | "/", [ p; expr ] ->
            AtomT
              ( To_aevent.pred_of_ocamlexpr p,
                match expr.pexp_desc with
                | Pexp_array es -> List.map To_aevent.func_of_ocamlexpr es
                | _ -> [ To_aevent.func_of_ocamlexpr expr ] )
        | "starT", [ t ] -> StarT (aux t)
        | "|||", [ t1; t2 ] -> UnionT (aux t1, aux t2)
        | _ ->
            _failatwith __FILE__ __LINE__
            @@ spf "of_ocamlexpr_aux: %s"
            @@ Pprintast.string_of_expression expr)
    | Pexp_sequence (t1, t2) -> ConcatT (aux t1, aux t2)
    | _ ->
        _failatwith __FILE__ __LINE__
        @@ spf "of_ocamlexpr_aux: %s"
        @@ Pprintast.string_of_expression expr
  in
  aux expr

let of_ocamlexpr = of_ocamlexpr_aux >> normalize_name_srt

let rec pprint_srl = function
  | AtomL p -> spf "%s" (To_aevent.pprint_pred p)
  | ConcatL (t1, t2) -> spf "(%s;%s)" (pprint_srl t1) (pprint_srl t2)
  | StarL t -> spf "(%s)*" (pprint_srl t)
  | UnionL (t1, t2) -> spf "(%s|%s)" (pprint_srl t1) (pprint_srl t2)
  | ExL (cx, t) ->
      spf "∃%s:%s.%s" cx.cx (pprint_parn @@ To_cty.layout cx.cty) (pprint_srl t)
  | InvImgL _ -> _failatwith __FILE__ __LINE__ "TODO: pprint InvImgL"
  | SfaL _ -> _failatwith __FILE__ __LINE__ "TODO: pprint SfaL"

let layout_srl = pprint_srl

let of_ocamlexpr_srl_aux expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_apply (func, args) -> (
        match (To_expr.id_of_ocamlexpr func, List.map snd args) with
        | "atomL", [ p ] -> AtomL (To_aevent.pred_of_ocamlexpr p)
        | "starL", [ t ] -> StarL (aux t)
        | "|||", [ t1; t2 ] -> UnionL (aux t1, aux t2)
        | _ ->
            _failatwith __FILE__ __LINE__
            @@ spf "of_ocamlexpr_aux: %s"
            @@ Pprintast.string_of_expression expr)
    | Pexp_sequence (t1, t2) -> ConcatL (aux t1, aux t2)
    | _ ->
        _failatwith __FILE__ __LINE__
        @@ spf "of_ocamlexpr_aux: %s"
        @@ Pprintast.string_of_expression expr
  in
  aux expr

let of_ocamlexpr_srl = of_ocamlexpr_srl_aux >> normalize_name_srl
