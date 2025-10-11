open Sugar

(* module Ax =  *)
module F (Ax : module type of Axiom.F (Lit.Lit)) = struct
  module P = struct
    include Ax

    let get_asm = get_uninterops >> get_related_assumption

    let constant_to_z3 ctx c =
      let open Constant in
      match c with
      | U | Tu _ | Dt _ ->
          _failatwith __FILE__ __LINE__ "unimp complex constant encoding"
      | B b -> Smtquery.bool_to_z3 ctx b
      | I i -> Smtquery.int_to_z3 ctx i

    let rec typed_lit_to_z3 ctx lit =
      match lit.x with
      | ATu _ | AProj _ -> _failatwith __FILE__ __LINE__ "die"
      | AC c -> constant_to_z3 ctx c
      | AVar x -> Smtquery.tpedvar_to_z3 ctx (lit.ty, x)
      | AAppOp (op, args) -> (
          let open Z3 in
          (* let args = *)
          (*   match args with [ { x = AC U; ty = Ty_unit } ] -> [] | _ -> args *)
          (* in *)
          let args = List.map (typed_lit_to_z3 ctx) args in
          match (op.x, args) with
          | Op.BuiltinOp "==", [ a; b ] -> Boolean.mk_eq ctx a b
          | Op.BuiltinOp "!=", [ a; b ] ->
              Boolean.mk_not ctx @@ Boolean.mk_eq ctx a b
          | Op.BuiltinOp "<=", [ a; b ] -> Arithmetic.mk_le ctx a b
          | Op.BuiltinOp ">=", [ a; b ] -> Arithmetic.mk_ge ctx a b
          | Op.BuiltinOp "<", [ a; b ] -> Arithmetic.mk_lt ctx a b
          | Op.BuiltinOp ">", [ a; b ] -> Arithmetic.mk_gt ctx a b
          | Op.BuiltinOp "+", [ a; b ] -> Arithmetic.mk_add ctx [ a; b ]
          | Op.BuiltinOp "-", [ a; b ] -> Arithmetic.mk_sub ctx [ a; b ]
          | Op.BuiltinOp "mod", [ a; b ] -> Arithmetic.Integer.mk_mod ctx a b
          | Op.BuiltinOp "*", [ a; b ] -> Arithmetic.mk_mul ctx [ a; b ]
          | Op.BuiltinOp "/", [ a; b ] -> Arithmetic.mk_div ctx a b
          | Op.BuiltinOp opname, args ->
              let () =
                if
                  List.exists (String.equal opname)
                    (MetaConfig.get_uninterops ())
                then ()
                else failwith (spf "unknown operator: %s" opname)
              in
              (* let () = Printf.printf ">>>> op(%s): %s\n" opname (Nt.layout op.ty) in *)
              let argsty, retty = Nt.destruct_arr_tp op.ty in
              let func = Smtquery.z3func ctx opname argsty retty in
              Z3.FuncDecl.apply func args
          | _ -> failwith @@ spf "unknown operator: %s" (Op.to_string op.x))

    let to_z3 ctx prop =
      let open Smtquery in
      let rec aux prop =
        match prop with
        | Implies (p1, p2) -> Z3.Boolean.mk_implies ctx (aux p1) (aux p2)
        | Ite (p1, p2, p3) -> Z3.Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
        | Not p -> Z3.Boolean.mk_not ctx (aux p)
        | And ps -> Z3.Boolean.mk_and ctx (List.map aux ps)
        | Or ps -> Z3.Boolean.mk_or ctx (List.map aux ps)
        | Iff (p1, p2) -> Z3.Boolean.mk_iff ctx (aux p1) (aux p2)
        | Forall (u, body) ->
            make_forall ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
        | Exists (u, body) ->
            make_exists ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
        | Lit lit -> typed_lit_to_z3 ctx lit #: Nt.bool_ty
      in
      aux prop
  end

  module R = struct
    include Nregex.T
    open Smtquery.Z3reg.F (Minterm.T)
    module RegZ3 = RegZ3BackendV2

    let parse_reg encoding reg =
      let rec aux reg =
        match reg with
        | Epsilon | Any | Empt -> ()
        | Minterm mt -> RegZ3.insert_mt encoding mt
        | Diff (r1, r2) ->
            aux r1;
            aux r2
        | Union rs -> List.iter aux rs
        | Intersect rs -> List.iter aux rs
        | Concat rs -> List.iter aux rs
        | Star r -> aux r
        | Complement r -> aux r
      in
      aux reg

    let get_size encoding reg =
      let rec aux reg =
        (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
        match reg with
        | Any -> RegZ3.get_cardinal encoding
        | Empt | Epsilon | Minterm _ -> 1
        | Diff (r1, r2) -> 1 + aux r1 + aux r2
        (* NOTE: z3 will raise exception when the length of the list < 2 *)
        | Union rs ->
            let bs = List.map aux rs in
            List.fold_left (fun sum n -> sum + n) 1 bs
        | Intersect rs ->
            let bs = List.map aux rs in
            List.fold_left (fun sum n -> sum + n) 1 bs
        | Concat rs ->
            let bs = List.map aux rs in
            List.fold_left (fun sum n -> sum + n) (List.length rs) bs
        | Star r -> 1 + aux r
        | Complement r ->
            let n = aux (Star Any) in
            1 + n + aux r
      in
      aux reg

    let merge_concat reg =
      let rec aux reg =
        match reg with
        | Any | Empt | Epsilon | Minterm _ -> reg
        | Diff (r1, r2) -> Diff (aux r1, aux r2)
        | Union rs -> Union (List.map aux rs)
        | Intersect rs -> Intersect (List.map aux rs)
        | Star r -> Star (aux r)
        | Complement r -> Complement (aux r)
        | Concat rs ->
            let rs = List.map aux rs in
            let rs =
              List.fold_left
                (fun res r ->
                  match r with Concat rs' -> res @ rs' | _ -> res @ [ r ])
                [] rs
            in
            (* let () = *)
            (*   Printf.printf "Concat: %s\n" @@ List.split_by " ;; " reg_to_string rs *)
            (* in *)
            Concat rs
      in
      aux reg

    open Z3

    let rec to_z3 ctx encoding reg =
      let rec aux reg =
        (* let () = Printf.printf "%s\n" @@ reg_to_string reg in *)
        let res =
          match reg with
          | Any -> RegZ3.get_any ctx encoding
          | Empt -> mk_empty ctx
          | Epsilon -> mk_epsilon ctx
          | Minterm mt -> RegZ3.mt_to_z3 ctx encoding mt
          | Diff (r1, r2) ->
              Seq.mk_re_intersect ctx
                [ aux r1; Seq.mk_re_complement ctx @@ aux r2 ]
          (* NOTE: z3 will raise exception when the length of the list < 2 *)
          | Union [] -> mk_empty ctx
          | Union [ r ] -> aux r
          | Union rs ->
              (* let () = Printf.printf "len(union rs) = %i\n" @@ List.length rs in *)
              Seq.mk_re_union ctx @@ List.map aux rs
          | Intersect [] -> _failatwith __FILE__ __LINE__ "die"
          | Intersect [ r ] -> aux r
          | Intersect rs ->
              (* let () = Printf.printf "len(intersect rs) = %i\n" @@ List.length rs in *)
              Seq.mk_re_intersect ctx @@ List.map aux rs
          | Concat [] -> _failatwith __FILE__ __LINE__ "die"
          | Concat [ r ] -> aux r
          | Concat rs -> concat_to_z3 ctx encoding rs
          (* let () = Printf.printf "len(concat rs) = %i\n" @@ List.length rs in *)
          (* let rs' = List.map aux rs in *)
          (* let () = *)
          (*   Printf.printf "%s\n" @@ List.split_by " ? " Expr.to_string rs' *)
          (* in *)
          (* Seq.mk_re_concat ctx rs' *)
          (* | Star (Complement Empt) -> mk_full ctx *)
          | Star r -> Seq.mk_re_star ctx @@ aux r
          (* | Complement Empt -> mk_full ctx *)
          | Complement r ->
              (* Seq.mk_re_complement ctx @@ aux r *)
              let al = aux (Star Any) in
              Seq.mk_re_intersect ctx [ al; Seq.mk_re_complement ctx @@ aux r ]
        in
        (* let () = *)
        (*   Printf.printf "[ENCODE] %s ===> %s\n" (reg_to_string reg) *)
        (*     (Expr.to_string res) *)
        (* in *)
        res
      in
      aux reg

    and concat_to_z3 ctx encoding rs =
      let acc_to_z3 ms =
        match ms with
        | [] -> None
        | [ m ] -> Some (RegZ3.mt_to_z3 ctx encoding m)
        | _ ->
            let str =
              String.concat "" @@ List.map (RegZ3.mt_to_string encoding) ms
            in
            Some (Seq.mk_seq_to_re ctx @@ Seq.mk_string ctx str)
      in
      let res, acc =
        List.fold_left
          (fun (res, acc) r ->
            match r with
            | Minterm m -> (res, acc @ [ m ])
            | Concat [] -> _failatwith __FILE__ __LINE__ "die"
            | _ -> (
                let r2 = to_z3 ctx encoding r in
                match acc_to_z3 acc with
                | None -> (res @ [ r2 ], [])
                | Some r1 -> (res @ [ r1; r2 ], [])))
          ([], []) rs
      in
      let res =
        match acc_to_z3 acc with None -> res | Some r -> res @ [ r ]
      in
      match res with
      | [] -> _failatwith __FILE__ __LINE__ "die"
      | [ r ] -> r
      | _ -> Seq.mk_re_concat ctx res

    let to_z3_two_reg ctx (r1, r2) =
      let encoding = RegZ3.init () in
      let () = parse_reg encoding r1 in
      let () = parse_reg encoding r2 in
      (encoding, to_z3 ctx encoding r1, to_z3 ctx encoding r2)

    let to_z3_one_reg ctx r =
      let encoding = RegZ3.init () in
      let () = parse_reg encoding r in
      let len = !(encoding.next) in
      let () =
        MetaConfig.show_log "smt_regex" @@ fun _ ->
        Printf.printf "RegZ3 len: %i\n" len
      in
      (* let () = if len > 200 then failwith "end" else () in *)
      let r = merge_concat r in
      (* let () = RegZ3.print_encoding encoding in *)
      (encoding, to_z3 ctx encoding r)
  end

  include Smtquery.F (P) (Minterm.T) (R)
end
