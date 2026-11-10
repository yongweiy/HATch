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
  let pcode = load_raw_code_from_file @@ MetaConfig.get_builtin_normal_type () in
  let opnctx = StructureRaw.mk_normal_top_ctx pcode in
  let opnctx = List.map ~f:(fun (x, ty) -> (Op.force_id_to_op x, ty)) opnctx in
  opnctx

let load_code_from_file qfile =
  let preds =
    load_raw_code_from_file @@ MetaConfig.get_builtin_automata_pred_type ()
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
          (optional_with_default 20 int)
          ~doc:
            "<int> Set the bound on the number of reduction steps during \
             symbolic execution"
      and no_derivative = flag "-no-deriv" no_arg ~doc:" Disable derivative"
      and append_bound =
        flag "-eff-append-bound"
          (optional_with_default 5 int)
          ~doc:
            "<int> Set the bound on the length of event sequences sampled from \
             SFA being appended during symbolic execution"
      and accel_bound =
        flag "-accel-bound"
          (optional_with_default 0 int)
          ~doc:
            "<int> Set the bound on the number of reduction steps within one \
             iteration to be accelerated"
      and empty_aware =
        flag "-empty-aware" no_arg
          ~doc:
            "Make derivative-based engine stop upon reaching bad state in SFA"
      and look_ahead =
        flag "-sfa-look-ahead"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the look-ahead depth for empty state in SFA during \
             symbolic execution"
      and mem_limit_gb =
        flag "-mem-limit-gb"
          (optional_with_default 64 int)
          ~doc:
            "<int> Heap cap in GiB per task; exceeding it reports \
             \"Out of memory\""
      in
      f meta_config_file source_file exec_bound (not no_derivative) append_bound
        empty_aware look_ahead accel_bound mem_limit_gb)

let cmd_infer_incor_config_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file)
      and unroll_bound =
        flag "-unroll-bound"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the bound on the number of times to unroll recursive \
             functions during type inference (default: 1)"
      in
      f meta_config_file source_file unroll_bound)

let cmd_infer_incor_config_source_with_witness summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file)
      and unroll_bound =
        flag "-unroll-bound"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the bound on the number of times to unroll recursive \
             functions during type inference (default: 1)"
      and no_witness =
        flag "-no-witness" no_arg
          ~doc:
            " Do not print the witness type (surface effect syntax) after the \
             inferred type"
      in
      f meta_config_file source_file unroll_bound (not no_witness))

let cmd_infer_incor_config_source_with_forward summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file)
      and unroll_bound =
        flag "-unroll-bound"
          (optional_with_default 1 int)
          ~doc:
            "<int> Set the bound on the number of times to unroll recursive \
             functions during type inference (default: 1)"
      and forward_steps =
        flag "-forward-steps"
          (optional_with_default 0 int)
          ~doc:
            "<int> Set the number of forward steps to take before backward \
             reasoning (default: 0, pure backward)"
      in
      f meta_config_file source_file unroll_bound forward_steps)

let cmd_config_ir_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and dir = anon ("representation_invariant_file" %: string)
      and name = anon ("source_code_file" %: string) in
      f meta_config_file dir name)
