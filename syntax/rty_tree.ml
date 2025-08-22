(* TODO the module should be parameterized by the extension of rty to hty *)
module SyntaxF
    (A : sig
      type sfa [@@deriving sexp]
    end)
    (T : sig
      type pred [@@deriving sexp]
      type ev [@@deriving sexp]
      type sft [@@deriving sexp]
    end)
    (L : Lit.T) =
struct
  open Sexplib.Std
  module Cty = Cty.F (L)
  include Cty

  module Trans = struct
    type t =
      | Explicit of T.sft
      | Admit of A.sfa
      | Append of T.ev
      | Reject of T.pred
    [@@deriving sexp]
  end

  module Eff = struct
    type atom = Id | Call of T.ev | Trans of Trans.t [@@deriving sexp]

    type t =
      | Atom of atom
      | Constrain of t * t
      | Bind of string ctyped * t
      | Guard of prop
      | Seq of t * t
      | Choice of t * t
    [@@deriving sexp]

    let is_identity = function Atom Id -> true | _ -> false
  end

  type rty = BaseRty of { cty : cty } | ArrRty of { arr : arr; rethty : hty }
  [@@deriving sexp]

  and arr =
    | NormalArr of string rtyped
    | GhostArr of string Nt.typed
    | ArrArr of rty
  [@@deriving sexp]

  and hty =
    | Rty of rty
    | Monad of monad
    | Htriple of htriple
    | Inter of hty * hty
  [@@deriving sexp]

  and monad = { ret : string rtyped; eff : Eff.t }
  and htriple = { pre : A.sfa; resrty : rty; post : A.sfa } [@@deriving sexp]
  and 'a rtyped = { rx : 'a; rty : rty } [@@deriving sexp]

  type 'a htyped = { hx : 'a; hty : hty } [@@deriving sexp]

  (* erase *)
  open Sugar

  let rec destruct_gvars_rty rty =
    match rty with
    | ArrRty { arr = GhostArr x; rethty = Rty rty } ->
        let gvars, rty = destruct_gvars_rty rty in
        (x :: gvars, rty)
    | _ -> ([], rty)

  let rec construct_gvars_rty gvars rty =
    match gvars with
    | [] -> rty
    | x :: gvars ->
        let rty = construct_gvars_rty gvars rty in
        ArrRty { arr = GhostArr x; rethty = Rty rty }

  let is_multi_args_rty rty =
    let gvars, rty = destruct_gvars_rty rty in
    match rty with
    | ArrRty { rethty = Rty (ArrRty _); _ } -> Some (gvars, rty)
    | _ -> None

  let rec erase_rty rty =
    let open Nt in
    match rty with
    | BaseRty { cty; _ } -> Cty.erase cty
    | ArrRty { arr; rethty } -> (
        let retnty = erase_hty rethty in
        match erase_arr arr with
        | None -> retnty
        | Some paranty -> mk_arr paranty retnty)

  and erase_arr = function
    | NormalArr { rty; _ } -> Some (erase_rty rty)
    | GhostArr _ -> None
    | ArrArr rty -> Some (erase_rty rty)

  and erase_hty rty =
    (* let open Nt in *)
    match rty with
    | Rty rty -> erase_rty rty
    | Monad { ret = { rty; _ }; _ } -> erase_rty rty
    | Htriple { resrty; _ } -> erase_rty resrty
    | Inter (hty1, hty2) ->
        let ty1 = erase_hty hty1 in
        let ty2 = erase_hty hty2 in
        let _ = _assert __FILE__ __LINE__ "eq" (Nt.eq ty1 ty2) in
        ty1

  let rtyped_erase { rx; rty } = Nt.{ x = rx; ty = erase_rty rty }

  let rty_to_cty rty =
    match rty with
    | BaseRty { cty } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let hty_to_htriple hty =
    match hty with
    | Htriple htriple -> htriple
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let hty_to_monad file line = function
    | Monad monad -> monad
    | Rty rty -> { ret = { rx = "ret"; rty }; eff = Eff.Atom Eff.Id }
    | _ -> _failatwith file line "die"

  let hty_to_rty file line = function
    | Rty rty -> rty
    | _ -> _failatwith file line "die"

  let htyped_force_to_rtyped file line { hx; hty } =
    match hty with
    | Rty rty -> { rx = hx; rty }
    | _ -> _failatwith file line "die"

  let rty_destruct_arr file line = function
    | ArrRty { arr; rethty } -> (arr, rethty)
    | _ -> _failatwith file line "die"

  let neg_rty file line = function
    | BaseRty { cty } -> BaseRty { cty = Cty.neg_cty cty }
    | _ -> _failatwith __FILE__ __LINE__ "die"
end
