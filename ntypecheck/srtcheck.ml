open Language
module Typectx = NTypectx
open Sugar
open RtyRaw.SRT

let rec check opctx ctx = function
  | AtomT (p, fs) ->
      AtomT
        ( Aeventcheck.check_pred opctx ctx p,
          List.map (Aeventcheck.check_func opctx ctx) fs )
  | StarT t -> StarT (check opctx ctx t)
  | ConcatT (t1, t2) -> ConcatT (check opctx ctx t1, check opctx ctx t2)
  | UnionT (t1, t2) -> UnionT (check opctx ctx t1, check opctx ctx t2)
  | ComposeT (t1, t2) -> ComposeT (check opctx ctx t1, check opctx ctx t2)
  | ExT (cx, t) ->
      let cx = { cx with cty = Ctycheck.check opctx ctx cx.cty } in
      let ctx' =
        Typectx.new_to_right ctx Nt.{ x = cx.cx; ty = Cty.erase cx.cty }
      in
      let t = check opctx ctx' t in
      ExT (cx, t)
  | SftT _ -> _failatwith __FILE__ __LINE__ "check: SFT not supported"

let rec check_srl opctx ctx = function
  | AtomL p -> AtomL (Aeventcheck.check_pred opctx ctx p)
  | StarL r -> check_srl opctx ctx r
  | ConcatL (r1, r2) -> ConcatL (check_srl opctx ctx r1, check_srl opctx ctx r2)
  | UnionL (r1, r2) -> UnionL (check_srl opctx ctx r1, check_srl opctx ctx r2)
  | InvImgL (t, r) -> InvImgL (check opctx ctx t, check_srl opctx ctx r)
  | ExL (cx, r) ->
      let cx = { cx with cty = Ctycheck.check opctx ctx cx.cty } in
      let ctx' =
        Typectx.new_to_right ctx Nt.{ x = cx.cx; ty = Cty.erase cx.cty }
      in
      let r = check_srl opctx ctx' r in
      ExL (cx, r)
  | SfaL _ -> _failatwith __FILE__ __LINE__ "check_srl: SFA not supported"
