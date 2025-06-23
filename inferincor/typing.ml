open Sugar
open Language
open Rty
open Srt

let refine_to_ceil : Nt.t -> rty = function
  | Ty_arrow _ -> _failatwith __FILE__ __LINE__ "TODO: refine_to_ceil"
  | ty -> mk_rty_var_sat_prop "_" #: ty mk_true

let under_to_over : rty -> rty = Fun.id

let of_ty_pre ty pre =
  { ret = "ret" #:: (refine_to_ceil ty); trans = PreAndPost (pre, mk_any) }

let of_rty rty = { ret = "ret" #:: rty; trans = PreToPost mk_ident }
let under_to_over_rtyped { rx; rty } = { rx; rty = under_to_over rty }

let existential { rx = cx; rty } =
  match rty with
  | ArrRty _ -> Fun.id
  | BaseRty { cty } -> (
      function[@warning "-8"]
      | { ret; trans = PreToPost (SftT (cxs, sft)) } ->
          assert (not @@ List.exists (String.equal cx) @@ fv_rty ret.rty);
          { ret; trans = PreToPost (SftT ((cx #::: cty) :: cxs, sft)) })

let multi_existential rxs = List.fold_right existential rxs

let inter_cty { v = v1; phi = phi1 } { v = v2; phi = phi2 } =
  assert (v1 = v2);
  { v = v1; phi = mk_and [ phi1; phi2 ] }

let inter_rty = function
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      BaseRty { cty = inter_cty cty1 cty2 }
  | _ -> _failatwith __FILE__ __LINE__ "inter_rty"

let[@warning "-8"] union_effty rctx
    {
      ret = { rx; rty = BaseRty { cty = { v = v1; phi = phi1 } } };
      trans = PreAndPost (pre, post);
    }
    {
      ret = { rx = rx'; rty = BaseRty { cty = { v = v2; phi = phi2 } } };
      trans = PreToPost trans;
    } =
  assert (rx = rx');
  assert (v1 = v2);
  assert (post = mk_any);
  let rty = BaseRty { cty = { v = v1; phi = mk_and [ phi1; phi2 ] } } in
  let ret = { rx; rty } in
  let rctx = RTypectx.new_to_right rctx ret in
  let trans' = restrict_domain ~rctx trans pre in
  assert (is_reachable trans');
  (* no need to restrict by range because in practice post is .* *)
  { ret; trans = PreToPost trans' }

