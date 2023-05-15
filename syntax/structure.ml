module F (L : Lit.T) = struct
  include Termlang.F (L)
  module R = Rty.F (L)
  module Equation = Algebraic.F (L)

  type rty_kind = RtyLib | RtyToCheck

  type entry =
    (* | Mps of string list *)
    | EquationEntry of Equation.equation
    | Type_dec of Type_dec.t
    | Func_dec of string Normalty.Ntyped.typed
    | FuncImp of { name : string; if_rec : bool; body : term typed }
    | Rty of { name : string; kind : rty_kind; rty : R.t }

  type structure = entry list

  (* open Sugar *)
  open Zzdatatype.Datatype

  let mk_normal_top_ctx_ = function
    | EquationEntry _ -> []
    | FuncImp _ -> []
    | Rty { name; kind; rty } -> (
        match kind with
        | RtyLib -> [ Normalty.Ntyped.(name #: (R.erase rty)) ]
        | RtyToCheck -> [])
    | Func_dec x -> [ x ]
    | Type_dec _ -> []

  let mk_normal_top_opctx_ = function
    | EquationEntry _ -> []
    | FuncImp _ -> []
    | Rty _ -> []
    | Func_dec _ -> []
    | Type_dec d -> Type_dec.mk_ctx_ d

  let mk_normal_top_ctx es = List.concat @@ List.map mk_normal_top_ctx_ es
  let mk_normal_top_opctx es = List.concat @@ List.map mk_normal_top_opctx_ es

  let map_imps f codes =
    List.map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } ->
            FuncImp { name; if_rec; body = f name if_rec body }
        | _ -> code)
      codes

  let map_rtys f codes =
    List.map
      (fun code ->
        match code with
        | Rty { name; kind; rty } -> Rty { name; kind; rty = f rty }
        | _ -> code)
      codes

  let filter_map_imps f codes =
    List.filter_map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } -> f name if_rec body
        | _ -> None)
      codes
end
