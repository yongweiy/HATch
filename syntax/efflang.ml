module F (L : Lit.T) = struct
  open Sexplib.Std
  open Sugar
  module Cty = Cty.F (L)
  open Cty
  module SFT = Sft.F (L)
  include SFT
  module Ax = Axiom.F (L)
  open Ax

  type eff_atom =
    | ECall of { op : string; args : lit typed list; ret : lit typed }
    | ETrans of sft
  [@@deriving sexp]

  type eff =
    | EAtom of eff_atom
    | EReach of eff
    | EBind of string ctyped * eff
    | EGuard of prop
    | ESeq of eff * eff
    | EChoice of eff * eff
  [@@warning "-37-34"] [@@deriving sexp]

  let rec normalize_name_eff = function
    | EBind ({ cx; cty }, eff) ->
        EBind ({ cx; cty = Cty.normalize_name cty }, normalize_name_eff eff)
    | EReach eff -> EReach (normalize_name_eff eff)
    | ESeq (eff1, eff2) ->
        ESeq (normalize_name_eff eff1, normalize_name_eff eff2)
    | EChoice (eff1, eff2) ->
        EChoice (normalize_name_eff eff1, normalize_name_eff eff2)
    | eff -> eff

  let subst_eff_atom yz = function
    | ECall { op; args; ret } ->
        let aux = subst_lit yz in
        ECall { op; args = List.map (( #-> ) aux) args; ret = aux #-> ret }
    | ETrans sft -> ETrans (subst_sft yz sft)

  let rec subst_eff yz = function
    | EAtom eff_atom -> EAtom (subst_eff_atom yz eff_atom)
    | EReach eff -> EReach (subst_eff yz eff)
    | EBind ({ cx; cty }, eff) ->
        EBind ({ cx; cty = Cty.subst yz cty }, subst_eff yz eff)
    | EGuard p -> EGuard (subst_prop yz p)
    | ESeq (eff1, eff2) -> ESeq (subst_eff yz eff1, subst_eff yz eff2)
    | EChoice (eff1, eff2) -> EChoice (subst_eff yz eff1, subst_eff yz eff2)

  let fv_eff_atom = function
    | ECall { args; ret; _ } -> List.concat_map fv_typed_lit (ret :: args)
    | ETrans sft -> fv_sft sft

  let rec fv_eff = function
    | EAtom eff_atom -> fv_eff_atom eff_atom
    | EReach eff -> fv_eff eff
    | EBind ({ cx; cty }, eff) ->
        Cty.fv cty @ List.filter (not << String.equal cx) @@ fv_eff eff
    | EGuard p -> fv_prop p
    | ESeq (eff1, eff2) -> fv_eff eff1 @ fv_eff eff2
    | EChoice (eff1, eff2) -> fv_eff eff1 @ fv_eff eff2
end
