module F (L : Lit.T) = struct
  include L
  open Sexplib.Std
  open Ppx_compare_lib.Builtin
  open Ppx_hash_lib.Std.Hash.Builtin
  open Sugar

  type prop =
    | Lit of lit
    | Implies of prop * prop
    | Ite of prop * prop * prop
    | Not of prop
    | And of prop list
    | Or of prop list
    | Iff of prop * prop
    | Forall of string Normalty.Ntyped.typed * prop
    | Exists of string Normalty.Ntyped.typed * prop
  [@@deriving sexp, compare, equal, hash]

  let get_cbool = function Lit (AC (Constant.B b)) -> Some b | _ -> None
  let mk_true = Lit mk_lit_true
  let mk_false = Lit mk_lit_false
  let is_true p = match get_cbool p with Some true -> true | _ -> false
  let is_false p = match get_cbool p with Some false -> true | _ -> false

  let mk_not = function
    | Not p -> p
    | p when is_true p -> mk_false
    | p when is_false p -> mk_true
    | p -> Not p

  let is_neg p1 p2 = equal_prop p1 (mk_not p2)

  let smart_and l =
    if List.exists is_false l then mk_false
    else
      match List.filter (fun p -> not (is_true p)) l with
      | [] -> mk_true
      | [ x ] -> x
      | [ x; y ] when x = y -> x
      | l -> And l

  let smart_or l =
    if List.exists is_true l then mk_true
    else
      match List.filter (fun p -> not (is_false p)) l with
      | [] -> mk_false
      | [ x ] -> x
      | l -> Or l

  let get_lits prop =
    let () =
      Env.show_log "gather" @@ fun _ -> Printf.printf ">>>>> get_lits:\n"
    in
    let rec aux e res =
      match e with
      | Lit (AC _) -> res
      | Lit lit -> (
          let litopt = get_non_unit_lit lit #: bool_ty in
          match litopt with None -> res | Some lit -> lit :: res)
      | Implies (e1, e2) -> aux e1 @@ aux e2 res
      | Ite (e1, e2, e3) -> aux e1 @@ aux e2 @@ aux e3 res
      | Not e -> aux e res
      | And es -> List.fold_right aux es res
      | Or es -> List.fold_right aux es res
      | Iff (e1, e2) -> aux e1 @@ aux e2 res
      | Forall _ -> _failatwith __FILE__ __LINE__ "die"
      | Exists _ -> _failatwith __FILE__ __LINE__ "die"
    in
    let (lits : lit list) = aux prop [] in
    Zzdatatype.Datatype.List.slow_rm_dup eq_lit lits

  let multi_exists l prop =
    List.fold_right (fun u prop -> Exists (u, prop)) l prop

  let multi_forall l prop =
    List.fold_right (fun u prop -> Forall (u, prop)) l prop

  let smart_add_to a prop =
    match get_cbool a with
    | Some true -> prop
    | Some false -> mk_false
    | None ->
        let props = match prop with And props -> props | _ -> [ prop ] in
        let atoms = match a with And atoms -> atoms | _ -> [ a ] in
        if List.exists (fun a -> List.exists (is_neg a) props) atoms then
          mk_false
        else
          smart_and @@ props
          @ List.filter
              (fun atom -> not @@ List.exists (equal_prop atom) props)
              atoms

  let smart_implies a prop =
    match get_cbool a with
    | Some true -> prop
    | Some false -> mk_true
    | None -> Implies (a, prop)

  let subst_prop (y, f) e =
    let rec aux e =
      match e with
      | Lit lit -> Lit (subst_lit (y, f) lit)
      | Implies (e1, e2) -> Implies (aux e1, aux e2)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Not e -> Not (aux e)
      | And es -> And (List.map aux es)
      | Or es -> Or (List.map aux es)
      | Iff (e1, e2) -> Iff (aux e1, aux e2)
      | Forall (u, body) ->
          if String.equal u.x y then e else Forall (u, aux body)
      | Exists (u, body) ->
          if String.equal u.x y then e else Exists (u, aux body)
    in
    aux e

  let fv_prop e =
    let rec aux e =
      match e with
      | Lit lit -> fv_lit lit
      | Implies (e1, e2) -> aux e1 @ aux e2
      | Ite (e1, e2, e3) -> aux e1 @ aux e2 @ aux e3
      | Not e -> aux e
      | And es -> List.concat_map aux es
      | Or es -> List.concat_map aux es
      | Iff (e1, e2) -> aux e1 @ aux e2
      | Forall (u, body) ->
          List.filter (fun x -> not (String.equal x u.x)) @@ aux body
      | Exists (u, body) ->
          List.filter (fun x -> not (String.equal x u.x)) @@ aux body
    in
    aux e

  let typed_fv_prop e =
    let rec aux e =
      match e with
      | Lit lit -> typed_fv_lit lit #: bool_ty
      | Implies (e1, e2) -> aux e1 @ aux e2
      | Ite (e1, e2, e3) -> aux e1 @ aux e2 @ aux e3
      | Not e -> aux e
      | And es -> List.concat_map aux es
      | Or es -> List.concat_map aux es
      | Iff (e1, e2) -> aux e1 @ aux e2
      | Forall (u, body) ->
          List.filter (fun x -> not (String.equal x.x u.x)) @@ aux body
      | Exists (u, body) ->
          List.filter (fun x -> not (String.equal x.x u.x)) @@ aux body
    in
    aux e

  let prop_multisubst = List.fold_right subst_prop
  let subst_prop_id (y, z) e = subst_prop (y, AVar z) e
  let multisubst_prop_id l e = List.fold_right subst_prop_id l e

  let get_eqprop_by_name prop x =
    match prop with Lit lit -> get_eqlit_by_name lit x | _ -> None

  let smart_multi_exists (l : 'a Lit.Ty.typed list) prop =
    let fvs = fv_prop prop in
    List.fold_right
      (fun (Normalty.Ntyped.{ x; ty } as u) prop ->
        if ty = Ty_unit || List.mem x fvs then prop else Exists (u, prop))
      l prop

  let smart_multi_forall (l : 'a Lit.Ty.typed list) prop =
    let fvs = fv_prop prop in
    List.fold_right
      (fun (Normalty.Ntyped.{ x; ty } as u) prop ->
        if ty = Ty_unit || List.mem x fvs then prop else Forall (u, prop))
      l prop

  let smart_sigma (u, xprop) prop =
    let Normalty.Ntyped.{ x; ty } = u in
    match ty with
    | Normalty.Ntyped.Ty_unit -> smart_add_to xprop prop
    | _ -> (
        match get_eqprop_by_name xprop x with
        | None -> Exists (u, smart_add_to xprop prop)
        | Some z -> subst_prop (x, z) prop)

  let smart_pi (u, xprop) prop =
    let Normalty.Ntyped.{ x; ty } = u in
    match ty with
    | Normalty.Ntyped.Ty_unit -> smart_implies xprop prop
    | _ -> (
        match get_eqprop_by_name xprop x with
        | None -> Forall (u, smart_implies xprop prop)
        | Some z -> subst_prop (x, z) prop)

  let find_boollit_assignment_from_prop_opt prop x =
    let rec aux e =
      match e with
      | And es -> (
          match List.filter_map aux es with [ s ] -> Some s | _ -> None)
      | Iff (Lit (AVar y), Lit lit) when String.equal x y -> Some lit
      | Iff (Lit lit, Lit (AVar y)) when String.equal x y -> Some lit
      | Iff _ -> None
      | Implies _ | Ite _ | Not _ | Forall _ | Exists _ | Or _ | Lit _ -> None
    in
    aux prop

  let find_boollit_assignment_from_prop prop x =
    match find_boollit_assignment_from_prop_opt prop x with
    | None -> _failatwith __FILE__ __LINE__ "die"
    | Some s -> s

  let find_intlit_assignment_from_prop prop x =
    let lits = get_lits prop in
    match List.filter_map (fun lit -> find_assignment_of_intvar lit x) lits with
    | [] -> _failatwith __FILE__ __LINE__ "die"
    | [ s ] -> s
    | _ -> _failatwith __FILE__ __LINE__ "die"

  open Zzdatatype.Datatype

  let get_uninterops prop =
    let rec aux e =
      match e with
      | Lit lit -> get_uninterops_from_lit lit
      | Implies (e1, e2) -> aux e1 @ aux e2
      | Ite (e1, e2, e3) -> aux e1 @ aux e2 @ aux e3
      | Not e -> aux e
      | And es -> List.concat_map aux es
      | Or es -> List.concat_map aux es
      | Iff (e1, e2) -> aux e1 @ aux e2
      | Forall (_, body) -> aux body
      | Exists (_, body) -> aux body
    in
    List.slow_rm_dup String.equal @@ aux prop

  (* let get_lits prop = *)
  (*   let rec aux e res = *)
  (*     match e with *)
  (*     | Lit (AC _) -> res *)
  (*     | Lit lit -> lit :: res *)
  (*     | Implies (e1, e2) -> aux e1 @@ aux e2 res *)
  (*     | Ite (e1, e2, e3) -> aux e1 @@ aux e2 @@ aux e3 res *)
  (*     | Not e -> aux e res *)
  (*     | And es -> List.fold_right aux es res *)
  (*     | Or es -> List.fold_right aux es res *)
  (*     | Iff (e1, e2) -> aux e1 @@ aux e2 res *)
  (*     | Forall _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*     | Exists _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*   in *)
  (*   let (lits : lit list) = aux prop [] in *)
  (*   Zzdatatype.Datatype.List.slow_rm_dup eq_lit lits *)

  let subst_lit_lit (lit1, prop) e =
    let rec aux e =
      match e with
      | Lit lit -> if eq_lit lit lit1 then prop else e
      | Implies (e1, e2) -> Implies (aux e1, aux e2)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Not e -> Not (aux e)
      | And es -> And (List.map aux es)
      | Or es -> Or (List.map aux es)
      | Iff (e1, e2) -> Iff (aux e1, aux e2)
      | Forall (u, body) -> Forall (u, aux body)
      | Exists (u, body) -> Exists (u, aux body)
    in
    aux e

  (* module Nt = Normalty.Ntyped *)

  let close_fv (x, phix) prop =
    if not (List.exists (String.equal x.Normalty.Ntyped.x) (fv_prop prop)) then
      prop
    else
      let lits = get_lits prop in
      let lits =
        List.filter_map
          (fun lit ->
            match find_assignment_of_intvar lit x.Normalty.Ntyped.x with
            | Some eqlit -> Some (lit, eqlit)
            | None -> None)
          lits
      in
      match lits with
      | [ (lit, eqlit) ] ->
          let prop =
            subst_lit_lit (lit, subst_prop (Common.v_name, eqlit) phix) prop
          in
          prop
      | _ -> Exists (x, smart_add_to phix prop)

  type pe = IsT | IsF | IsOthers

  let pe_prop prop =
    if is_true prop then IsT else if is_false prop then IsF else IsOthers

  let simpl prop =
    let rec aux e =
      match e with
      | Lit _ -> e
      | Implies (e1, e2) -> (
          let e1, e2 = map2 aux (e1, e2) in
          match (pe_prop e1, pe_prop e2) with
          | IsT, _ -> e2
          | IsF, _ -> mk_true
          | _, IsT -> mk_true
          | _, IsF -> aux (Not e1)
          | _, _ -> Implies (e1, e2))
      | Ite (e1, e2, e3) -> (
          let e1, e2, e3 = map3 aux (e1, e2, e3) in
          match pe_prop e1 with
          | IsT -> e2
          | IsF -> e3
          | _ -> (
              match (pe_prop e2, pe_prop e3) with
              | IsT, IsT -> mk_true
              | IsT, IsF -> e1
              | IsF, IsT -> aux (Not e1)
              | IsF, IsF -> mk_false
              | _, _ -> Ite (e1, e2, e3)))
      | Not e -> Not (aux e)
      | And es -> And (List.map aux es)
      | Or es -> Or (List.map aux es)
      | Iff (e1, e2) -> Iff (aux e1, aux e2)
      | Forall (u, body) -> Forall (u, aux body)
      | Exists (u, body) -> Exists (u, aux body)
    in
    aux prop
end
