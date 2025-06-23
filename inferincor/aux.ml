open Sugar
open Language
open TypedCoreEff
open Rty

let error_cty ({ v; phi } as cty) =
  match v.ty with
  | Nt.Ty_constructor (err, []) when String.equal err "err" ->
      Error { v = { v with ty = Nt.Ty_unit }; phi }
  | _ -> Ok cty

let error_rty = function
  | BaseRty { cty } -> (
      match error_cty cty with
      | Error cty -> Error (BaseRty { cty })
      | Ok cty -> Ok (BaseRty { cty }))
  | arrrty -> Ok arrrty

let append_rctx rctx rtyped =
  match rctx with
  | Ok rctx -> (
      match rtyped with
      | Ok rtyped -> Ok (rctx @ [ rtyped ])
      | Error rtyped -> Error (rctx @ [ rtyped ]))
  | Error rctx -> Error rctx
