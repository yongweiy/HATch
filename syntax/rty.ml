module F (L : Lit.T) = struct
  open Sexplib.Std
  include Cty.F (L)

  type ou = Over | Under [@@deriving sexp]

  type pty =
    | BasePty of { ou : ou; cty : cty }
    | TuplePty of pty list
    | ArrPty of { rarg : string option ptyped; retrty : rty }

  and rty =
    | Pty of pty
    | Regty of regex Nt.typed
    | Sigmaty of { localx : string typed; rty : rty }
  [@@deriving sexp]

  and sevent =
    | GuardEvent of prop
    | RetEvent of pty
    | EffEvent of { op : string; vs : string Nt.typed list; phi : prop }

  and regex =
    | EpsilonA
    | EventA of sevent
    | LorA of regex * regex
    | LandA of regex * regex
    | SeqA of regex * regex
    | StarA of regex

  and 'a typed = { x : 'a; ty : rty }
  and 'a ptyped = { px : 'a; pty : pty } [@@deriving sexp]

  type t = rty
  type 'a rtyped = 'a typed

  open Sugar

  let ret_name = "Ret"
  let guard_name = "Guard"
  let vs_names n = List.init n (fun i -> spf "%s%i" v_name i)

  (* NOTE: Gurad is not a real event, thus it has no op name *)
  let se_get_op = function
    | RetEvent _ -> ret_name
    | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
    | EffEvent { op; _ } -> op

  let compare_pty l1 l2 = Sexplib.Sexp.compare (sexp_of_pty l1) (sexp_of_pty l2)
  let eq_pty l1 l2 = 0 == compare_pty l1 l2

  let ou_eq a b =
    match (a, b) with Over, Over | Under, Under -> true | _ -> false

  let ou_flip = function Over -> Under | Under -> Over

  let pty_flip = function
    | BasePty { ou; cty } -> BasePty { ou = ou_flip ou; cty }
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rty_flip = function
    | Pty pty -> Pty (pty_flip pty)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let ( #: ) x ty = { x; ty }
  let ( #:: ) px pty = { px; pty }
  let ( #-> ) f { x; ty } = { x = f x; ty }
  let ( #--> ) f { px; pty } = { px = f px; pty }

  (* subst *)

  let rec subst_pty (y, z) rty =
    let rec aux rty =
      match rty with
      | BasePty { cty; ou } -> BasePty { cty = subst_cty (y, z) cty; ou }
      | TuplePty ptys -> TuplePty (List.map aux ptys)
      | ArrPty { rarg; retrty } -> (
          let rarg = rarg.px #:: (aux rarg.pty) in
          match rarg.px with
          | Some x when String.equal y x -> ArrPty { rarg; retrty }
          | _ -> ArrPty { rarg; retrty = subst (y, z) retrty })
    in
    aux rty

  and subst_sevent (y, z) sevent =
    match sevent with
    | GuardEvent phi -> GuardEvent (subst_prop (y, z) phi)
    | RetEvent pty -> RetEvent (subst_pty (y, z) pty)
    | EffEvent { op; vs; phi } ->
        if List.exists (fun x -> String.equal x.Nt.x y) vs then
          EffEvent { op; vs; phi }
        else EffEvent { op; vs; phi = subst_prop (y, z) phi }

  and subst_regex (y, z) regex =
    let rec aux regex =
      match regex with
      | EpsilonA -> EpsilonA
      | EventA se -> EventA (subst_sevent (y, z) se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
    in
    aux regex

  and subst (y, z) = function
    | Pty pty -> Pty (subst_pty (y, z) pty)
    | Regty regex -> Regty Nt.((subst_regex (y, z)) #-> regex)
    | Sigmaty { localx; rty } ->
        let localx = localx.x #: (subst (y, z) localx.ty) in
        let rty = if String.equal y localx.x then rty else subst (y, z) rty in
        Sigmaty { localx; rty }

  let subst_rty = subst

  let subst_id (y, z) rty =
    let z = AVar z in
    subst (y, z) rty

  (* fv *)

  let rec fv_pty rty =
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> fv_cty cty
      | TuplePty ptys -> List.concat_map aux ptys
      | ArrPty { rarg; retrty } ->
          let argfv = aux rarg.pty in
          let retfv =
            match rarg.px with
            | Some u -> List.filter (fun x -> String.equal x u) @@ fv retrty
            | None -> fv retrty
          in
          argfv @ retfv
    in
    aux rty

  and fv_sevent sevent =
    match sevent with
    | GuardEvent phi -> fv_prop phi
    | RetEvent pty -> fv_pty pty
    | EffEvent { vs; phi; _ } ->
        List.filter (fun y -> List.exists (fun x -> String.equal x.Nt.x y) vs)
        @@ fv_prop phi

  and fv_regex regex =
    let rec aux regex =
      match regex with
      | EpsilonA -> []
      | EventA se -> fv_sevent se
      | LorA (t1, t2) -> aux t1 @ aux t2
      | LandA (t1, t2) -> aux t1 @ aux t2
      | SeqA (t1, t2) -> aux t1 @ aux t2
      | StarA t -> aux t
    in
    aux regex

  and fv = function
    | Pty pty -> fv_pty pty
    | Regty regex -> fv_regex regex.Nt.x
    | Sigmaty { localx; rty } ->
        fv localx.ty @ List.filter (fun x -> String.equal x localx.x) @@ fv rty

  (* erase *)

  let rec erase_pty rty =
    let open Nt in
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> erase_cty cty
      | TuplePty ptys -> Ty_tuple (List.map aux ptys)
      | ArrPty { rarg; retrty } -> mk_arr (aux rarg.pty) (erase retrty)
    in
    aux rty

  and erase = function
    | Pty pty -> erase_pty pty
    | Regty regex -> regex.Nt.ty
    | Sigmaty { rty; _ } -> erase rty

  let ptyped_opt_erase { px; pty } =
    match px with None -> None | Some x -> Some Nt.{ x; ty = erase_pty pty }

  let typed_erase { x; ty } = Nt.{ x; ty = erase ty }

  let pty_to_ret_rty pty =
    Regty Nt.{ x = EventA (RetEvent pty); ty = erase_pty pty }

  let typed_force_to_ptyped file line { x; ty } =
    match ty with
    | Pty pty -> { px = x; pty }
    | _ -> _failatwith file line "die"

  (* gather lits/rtys *)

  open Zzdatatype.Datatype

  let get_lits_from_sevent sevent =
    match sevent with
    | GuardEvent phi ->
        let global_lits = P.get_lits phi in
        Some (guard_name, global_lits, [])
    | RetEvent _ -> None
    | EffEvent { op; phi; vs } ->
        let vs = List.map (fun x -> x.Nt.x) vs in
        let is_contain_local_free lit =
          match List.interset ( == ) vs @@ P.fv_lit lit with
          | [] -> false
          | _ -> true
        in
        let lits = P.get_lits phi in
        let local_lits, global_lits =
          List.partition is_contain_local_free lits
        in
        Some (op, global_lits, local_lits)

  let get_lits_from_regex regex =
    let update_local m (op, lits) =
      StrMap.update op
        (fun lits' ->
          match lits' with
          | None -> Some lits
          | Some lits' -> Some (List.slow_rm_dup P.eq_lit (lits @ lits')))
        m
    in
    let update_global m lits = List.slow_rm_dup P.eq_lit (lits @ m) in
    let rec aux regex (global_m, local_m) =
      match regex with
      | EpsilonA -> (global_m, local_m)
      | EventA se -> (
          match get_lits_from_sevent se with
          | None -> (global_m, local_m)
          | Some (op, global_lits, _) when String.equal op guard_name ->
              (update_global global_m global_lits, local_m)
          | Some (op, global_lits, local_lits) ->
              ( update_global global_m global_lits,
                update_local local_m (op, local_lits) ))
      | LorA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m)
      | LandA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m)
      | SeqA (t1, t2) -> aux t1 @@ aux t2 (global_m, local_m)
      | StarA t -> aux t (global_m, local_m)
    in
    aux regex ([], StrMap.empty)

  let get_ptys_from_sevent sevent =
    match sevent with RetEvent pty -> [ pty ] | _ -> []

  let get_ptys_from_regex regex =
    let rec aux regex res =
      match regex with
      | EpsilonA -> res
      | EventA se -> res @ get_ptys_from_sevent se
      | LorA (t1, t2) -> aux t1 @@ aux t2 res
      | LandA (t1, t2) -> aux t1 @@ aux t2 res
      | SeqA (t1, t2) -> aux t1 @@ aux t2 res
      | StarA t -> aux t res
    in
    List.slow_rm_dup eq_pty @@ aux regex []

  (* normalize name *)

  let rec normalize_name_pty tau1 =
    match tau1 with
    | BasePty { ou; cty } -> BasePty { ou; cty = normalize_name_cty cty }
    | TuplePty tys -> TuplePty (List.map normalize_name_pty tys)
    | ArrPty { rarg; retrty } ->
        let rarg = rarg.px #:: (normalize_name_pty rarg.pty) in
        let retrty = normalize_name_rty retrty in
        ArrPty { rarg; retrty }

  and normalize_name_sevent = function
    | GuardEvent phi -> GuardEvent phi
    | RetEvent pty -> RetEvent (normalize_name_pty pty)
    | EffEvent { op; vs; phi } ->
        let vs' = vs_names (List.length vs) in
        let tmp = _safe_combine __FILE__ __LINE__ vs vs' in
        let phi =
          List.fold_left
            (fun phi (x', x) -> P.subst_prop_id (x'.Nt.x, x) phi)
            phi tmp
        in
        let vs = List.map (fun (v, x) -> Nt.{ x; ty = v.ty }) tmp in
        EffEvent { op; vs; phi }

  and noralize_name_regex regex =
    let rec aux regex =
      match regex with
      | EpsilonA -> regex
      | EventA se -> EventA (normalize_name_sevent se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
    in
    aux regex

  and normalize_name_rty tau =
    match tau with
    | Pty tau -> Pty (normalize_name_pty tau)
    | Regty regex -> Regty Nt.(noralize_name_regex #-> regex)
    | Sigmaty { localx; rty } ->
        let localx = localx.x #: (normalize_name_rty localx.ty) in
        Sigmaty { localx; rty = normalize_name_rty rty }

  (* unify name *)

  let rec unify_name_pty (tau1, tau2) =
    match (tau1, tau2) with
    | BasePty _, BasePty _ -> (tau1, tau2)
    | TuplePty tys1, TuplePty tys2 ->
        let tys1, tys2 =
          List.split @@ List.map unify_name_pty
          @@ _safe_combine __FILE__ __LINE__ tys1 tys2
        in
        (TuplePty tys1, TuplePty tys2)
    | ( ArrPty { rarg = rarg1; retrty = retrty1 },
        ArrPty { rarg = rarg2; retrty = retrty2 } ) ->
        let pty1, pty2 = unify_name_pty (rarg1.pty, rarg2.pty) in
        let (rarg1, rarg2), retrty2 =
          match (rarg1.px, rarg2.px) with
          | None, None -> ((None #:: pty1, None #:: pty2), retrty2)
          | Some x1, Some x2 ->
              ( ((Some x1) #:: pty1, (Some x1) #:: pty2),
                subst_id (x2, x1) retrty2 )
          | _, _ -> _failatwith __FILE__ __LINE__ "?"
        in
        let retrty1, retrty2 = unify_name_rty (retrty1, retrty2) in
        ( ArrPty { rarg = rarg1; retrty = retrty1 },
          ArrPty { rarg = rarg2; retrty = retrty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_rty (tau1, tau2) =
    match (tau1, tau2) with
    | Pty tau1, Pty tau2 ->
        let tau1, tau2 = unify_name_pty (tau1, tau2) in
        (Pty tau1, Pty tau2)
    | Regty _, Regty _ -> (tau1, tau2)
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  let mk_unit_under_pty_from_prop phi =
    BasePty { ou = Under; cty = mk_unit_cty_from_prop phi }

  let mk_unit_under_rty_from_prop phi = Pty (mk_unit_under_pty_from_prop phi)
  let default_ty = mk_unit_under_rty_from_prop mk_true
  let mk_noty x = { x; ty = default_ty }
  let xmap f { x; ty } = { x = f x; ty }
  let is_base_pty = function BasePty _ -> true | _ -> false
  let is_overbase_pty = function BasePty { ou = Over; _ } -> true | _ -> false

  let is_underbase_pty = function
    | BasePty { ou = Under; _ } -> true
    | _ -> false

  (* mk bot/top *)

  let rec mk_bot_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_top_pty t1 in
        let retrty = Pty (mk_bot_pty t2) in
        ArrPty { rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_bot_pty tys)
    | _ -> BasePty { ou = Under; cty = mk_bot_cty t }

  and mk_top_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_bot_pty t1 in
        let retrty = Pty (mk_top_pty t2) in
        ArrPty { rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_top_pty tys)
    | _ -> BasePty { ou = Under; cty = mk_top_cty t }

  let eq tau1 tau2 =
    0 == Sexplib.Sexp.compare (sexp_of_rty tau1) (sexp_of_rty tau2)

  let is_arr_pty = function ArrPty _ -> true | _ -> false

  (* dummy interfaces *)
  let is_basic_tp _ = _failatwith __FILE__ __LINE__ "never happen"
  let is_dt _ = _failatwith __FILE__ __LINE__ "never happen"
  let destruct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let construct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify _ _ = _failatwith __FILE__ __LINE__ "unimp"
  let to_smttyped _ = _failatwith __FILE__ __LINE__ "unimp"
  let typed_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_typed _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify_ _ = _failatwith __FILE__ __LINE__ "unimp"

  let destruct_arr_one rty =
    match rty with
    | ArrPty { rarg; retrty } -> (rarg, retrty)
    | _ -> _failatwith __FILE__ __LINE__ ""

  let get_argty rty =
    match rty with
    | Pty rty ->
        let rarg, _ = destruct_arr_one rty in
        Pty rarg.pty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let get_retty rty =
    match rty with
    | Pty rty ->
        let _, retrty = destruct_arr_one rty in
        retrty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let snd_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let fst_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let bool_ty = default_ty
  let mk_tuple _ = _failatwith __FILE__ __LINE__ "unimp"
  let mk_arr _ = _failatwith __FILE__ __LINE__ "unimp"
  let int_ty = default_ty
  let unit_pty = BasePty { ou = Under; cty = mk_unit_cty_from_prop mk_true }
  let unit_ty = Pty unit_pty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
