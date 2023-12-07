open Language
module RCtx = RTypectx
module ROpCtx = ROpTypectx
open Rty
open Sugar

let layout_comp = Denormalize.layout_comp
let layout_value = Denormalize.layout_value

type typectx = {
  rctx : RCtx.ctx;
  opctx : ROpCtx.ctx;
}

let typectx_new_to_right typectx (binding : string rtyped) =
  { typectx with rctx = RCtx.new_to_right typectx.rctx binding }

let typectx_newopt_to_right typectx binding =
  match binding with
  | None -> typectx
  | Some binding -> typectx_new_to_right typectx binding

let typectx_new_to_rights typectx (binding : string rtyped list) =
  List.fold_left
    (fun typectx x -> typectx_new_to_right typectx x)
    typectx binding

let print_typectx typectx =
  Env.show_debug_typing (fun () ->
      (* Pp.printf "@{<bold>E:@} %s\n" "omitted"; *)
      (* Pp.printf "@{<bold>Op:@} %s\n" "omitted"; *)
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l typectx.rctx))

let print_subtyping_srl_str typectx (srl1, srl2) =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>Subtyping SRL:@}\n";
      Pp.printf "@{<bold>R:@} %s\n" (RCtx.layout_typed_l typectx.rctx);
      Pp.printf "⊢ @{<hi_magenta>%s@}\n⊆@{<cyan>%s@}\n" srl1 srl2)

let print_subtyping_srl typectx (srl1, srl2) =
  print_subtyping_srl_str typectx (layout_regex srl1, layout_regex srl2)

let subtyping_srl_bool file line typectx (srl1, srl2) =
  Env.show_debug_typing (fun _ -> print_subtyping_srl typectx (srl1, srl2));
  let runtime, res =
    Sugar.clock (fun _ -> Subtyping.sub_srl_bool typectx.rctx (srl1, srl2))
  in
  Env.show_debug_stat (fun _ ->
      Pp.printf "@{<bold>subtyping_srl_bool: @}%f\n" runtime);
  if not res then
    Env.show_debug_typing (fun () ->
        Pp.printf "@{<orange> subtyping_srl failed at [%s::%i]@}\n" file line);
  res

let print_typing_rule file line funcname rule =
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<bold>%s::%s@}(%s:%i)\n" funcname rule file line)

let print_exec_info file line rulename typectx comp sfa =
  print_typing_rule file line "Exec" rulename;
  print_typectx typectx;
  Env.show_debug_typing (fun () ->
      Pp.printf "@{<cyan>[%s]@}\n" @@ layout_regex sfa;
      Pp.printf "⇝ @{<hi_magenta>%s@} "
        (short_str (Env.get_max_printing_size ()) @@ layout_comp comp))

let unify_var_arr_ret y (arr, rethty) =
  match arr with
  | NormalArr x ->
      let rethty = subst_hty_id (x.rx, y) rethty in
      (Some { rx = y; rty = x.rty }, rethty)
  | GhostArr _ -> _failatwith __FILE__ __LINE__ "die"
  | ArrArr _ -> (None, rethty)

let unify_var_func_rty y hty =
  let arr, rethty = rty_destruct_arr __FILE__ __LINE__ hty in
  unify_var_arr_ret y (arr, rethty)
