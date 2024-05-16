open Core

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

type format = Raw | Typed | MonadicNormalForm

open Language

let load_raw_code_from_file qfile =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  code

let load_builtin_opctx () =
  let pcode = load_raw_code_from_file @@ Env.get_builtin_normal_type () in
  let opnctx = StructureRaw.mk_normal_top_ctx pcode in
  let opnctx = List.map ~f:(fun (x, ty) -> (Op.force_id_to_op x, ty)) opnctx in
  opnctx

let load_code_from_file qfile =
  let preds =
    load_raw_code_from_file @@ Env.get_builtin_automata_pred_type ()
  in
  StructureRaw.ltlf_to_srl @@ StructureRaw.inline_ltlf_pred @@ preds
  @ load_raw_code_from_file qfile

let load_typed_rtys_from_file opnctx file =
  let code = load_code_from_file file in
  let code = Ntypecheck.opt_to_typed_structure opnctx [] code in
  RTypectx.from_code code

let load_axioms_from_file opnctx file =
  let code = load_code_from_file file in
  let code = Ntypecheck.opt_to_typed_structure opnctx [] code in
  Structure.mk_axioms code

let cmd_config_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      f meta_config_file source_file)

let cmd_symb_exec_config_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file)
      and exec_bound =
        flag "-exec-bound"
          (optional_with_default 10 int)
          ~doc:
            "<int> Set the bound on the number of reduction steps during \
             symbolic execution"
      and no_derivative = flag "-no-deriv" no_arg ~doc:" Disable derivative"
      and append_bound =
        flag "-eff-append-bound"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the bound on the length of event sequences sampled from \
             SFA being appended during symbolic execution"
      and accel_bound =
        flag "-accel-bound"
          (optional_with_default 5 int)
          ~doc:
            "<int> Set the bound on the number of reduction steps within one \
             iteration to be accelerated"
      and look_ahead =
        flag "-sfa-look-ahead"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the look-ahead depth for empty state in SFA during \
             symbolic execution"
      in
      f meta_config_file source_file exec_bound (not no_derivative) append_bound
        look_ahead accel_bound)

let cmd_config_ir_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and dir = anon ("representation_invariant_file" %: string)
      and name = anon ("source_code_file" %: string) in
      f meta_config_file dir name)
