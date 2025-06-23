module F (L : Lit.T) = struct
  open Sexplib.Std
  include Cty.F (L)
  module Ax = Axiom.F (L)
  include Ax

  type eff =
    | ECall of { op : string; args : L.t list; ret : L.t }
    | EReach of eff
    | EBind of string ctyped * eff
    | EGuard of prop
    | ESeq of eff * eff
    | EChoice of eff * eff
  [@@warning "-37-34"] [@@deriving sexp]
end
