module F (L : Lit.T) = struct
  open Sexplib.Std
  module Ax = Axiom.F (L)
  include Ax

  type cty = { v : string Nt.typed; phi : prop } [@@deriving sexp]
  type 'a ctyped = { cx : 'a; cty : cty }

  (* open Sugar *)

  let v_name = "v"
  let ( #::: ) cx cty = { cx; cty }
  let ( #---> ) f { cx; cty } = { cx = f cx; cty }

  let cty_typed_to_prop { cx; cty = { v; phi } } =
    let Nt.{ x; ty } = v in
    (Nt.{ x = cx; ty }, P.subst_prop_id (x, cx) phi)

  let add_prop_to_cty phi cty = { cty with phi = smart_and [ cty.phi; phi ] }

  (* subst *)
  let subst (y, replacable) { v; phi } =
    if String.equal y v.Nt.x then { v; phi }
    else { v; phi = subst_prop (y, replacable) phi }

  let subst_id (y, z) cty =
    let z = AVar z in
    subst (y, z) cty

  (* fv *)
  let fv { v; phi } = List.filter (fun x -> String.equal x v.x) @@ fv_prop phi

  (* erase *)

  (* open Zzdatatype.Datatype *)

  let erase { v; _ } = v.Nt.ty

  (* normalize name *)

  let normalize_name { v; phi } =
    let phi = P.(subst_prop_id (v.x, v_name) phi) in
    let v = Nt.{ x = v_name; ty = v.ty } in
    { v; phi }

  (* mk bot/top *)

  let mk_from_prop ty phif =
    let v = Nt.(v_name #: ty) in
    { v; phi = phif v }

  let mk_unit_from_prop phi = Nt.{ v = v_name #: Ty_unit; phi }
  let mk_bot nt = Nt.{ v = v_name #: nt; phi = mk_false }
  let mk_top nt = Nt.{ v = v_name #: nt; phi = mk_true }

  let join_cty cty1 cty2 =
    let { v = v1; phi = phi1 } = cty1 in
    let { v = v2; phi = phi2 } = cty2 in
    assert (String.equal v1.x v2.x);
    assert (Nt.eq v1.ty v2.ty);
    { v = v1; phi = smart_and [ phi1; phi2 ] }
end
