(** Witness types in the surface effect language, in the form of the paper.

    [Weaken.weaken_pure] answers a query type with an algorithmic witness: the
    query's input refinements, a return refinement, and an effect that binds
    every intermediate value existentially in front of [Admit (pre); path].
    Here [path] is the sequence of library calls along the execution that the
    backward search ([Backwards.run]) chose (one case of the inferred ⊕), and
    [pre] is one path of the composed (program ; query) SFT that
    [Sft.find_witness] found: an incoming trace from which the query is
    reached.

    This module reads that result back as a witness type of the declarative
    system in the shape of the paper's witnesses (Sec. 2, [type:else-refined]
    in Sec. 4):

    {v
      x1:{..} -> ... -> {v:b | v = e} !
        reach (fun () -> k) ();   (* test of the trace before the call *)
        <path>                    (* the trace the application produces *)
    v}

    and prints it in the surface syntax of [{ ret = ...; eff = ... }]
    specifications, so that the query and the witness share one language:

    {v
      surface                             paper
      let (x : T) = (phi : [%v: T]) in e   x <- havoc_T; assume phi[x/v]; e
      Guard (phi)                         assume phi
      Op (a1, ..., an, r)                 y <- op a1 ... an; assume (y = r)
      e1; e2                              sequencing (bind, result discarded)
      Reach (fun () -> k) ()              reach (fun () -> k) ()  = <k>
    v}

    [Reach] has no counterpart in the surface syntax, which only offers the
    query form [Constrain (pre, post)]; inside it, [k] is a Boolean query in
    the same notation as the components of [Constrain].

    Every rewrite preserves the behaviors the witness claims: binders and
    assumptions do not touch the trace, so they commute with library calls;
    an existential fixed by an equality is replaced by its definition (the
    Skolem step of Rule JoinEffFO), and so is the return value when it is
    fixed to a term over the parameters (ibid.). *)

open Sugar
open Language
open Rty
module P = Rty.P

(* ------------------------------------------------------------------------ *)
(* Witness representation                                                    *)

type havoc = { hx : string; hty : Nt.t; hphi : prop  (** over [v_name] *) }

type step =
  | Havoc of havoc
  | Assume of prop
  | Call of Sft.ev
  | Presume of Eff.t
      (** [reach (fun () -> k) ()]: the may-test of [k] on the current trace *)

type t = {
  name : string;
  params : string rtyped list;
  ret : string * cty;
  steps : step list;
  found_trace : regex list;
      (** the incoming trace the search found (chronological), which
          discharges the presumption *)
}

exception Unsupported of string

let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

(* ------------------------------------------------------------------------ *)
(* Logic helpers                                                             *)

let conjuncts (p : prop) : prop list =
  let rec aux p =
    match p with
    | P.And ps -> List.concat_map aux ps
    | _ when P.is_true p -> []
    | _ -> [ p ]
  in
  aux p

let mk_conj (ps : prop list) : prop = P.smart_and ps

(** [Some (a, b)] if [p] is the equality [a == b] *)
let as_eq (p : prop) =
  match p with
  | P.Lit (P.AAppOp (op, [ a; b ])) when Op.id_eq_op op.x -> Some (a, b)
  | _ -> None

let op_name (op : Op.t typed) =
  match op.x with Op.BuiltinOp s -> Some s | _ -> None

(** Evaluate ground integer arithmetic. *)
let rec fold_lit (l : P.lit) : P.lit =
  match l with
  | P.AAppOp (op, args) -> (
      let args = List.map (fun (a : P.lit typed) -> { a with x = fold_lit a.x }) args in
      match (op_name op, List.map (fun (a : P.lit typed) -> a.x) args) with
      | Some "+", [ P.AC (Constant.I a); P.AC (Constant.I b) ] ->
          P.AC (Constant.I (a + b))
      | Some "-", [ P.AC (Constant.I a); P.AC (Constant.I b) ] ->
          P.AC (Constant.I (a - b))
      | Some "*", [ P.AC (Constant.I a); P.AC (Constant.I b) ] ->
          P.AC (Constant.I (a * b))
      | _ -> P.AAppOp (op, args))
  | P.ATu ls -> P.ATu (List.map (fun (a : P.lit typed) -> { a with x = fold_lit a.x }) ls)
  | P.AProj (a, i) -> P.AProj ({ a with x = fold_lit a.x }, i)
  | P.AC _ | P.AVar _ -> l

(** Propositional simplification, ground arithmetic and reflexivity of
    equality; all equivalences. *)
let rec simp (p : prop) : prop =
  match p with
  | P.Lit l -> (
      let l = fold_lit l in
      let p = P.Lit l in
      match l with
      | P.AAppOp (op, [ a; b ]) -> (
          match (op_name op, a.x, b.x) with
          | Some "==", a, b when P.eq_lit a b -> P.mk_true
          | Some "==", P.AC c1, P.AC c2 ->
              if Constant.equal c1 c2 then P.mk_true else P.mk_false
          | Some ("<" | ">" | "<=" | ">=" as o), P.AC (Constant.I a), P.AC (Constant.I b)
            ->
              let r =
                match o with
                | "<" -> a < b
                | ">" -> a > b
                | "<=" -> a <= b
                | _ -> a >= b
              in
              if r then P.mk_true else P.mk_false
          | _ -> p)
      | _ -> p)
  | P.Not q -> P.mk_not (simp q)
  | P.And ps -> P.smart_and (List.concat_map conjuncts (List.map simp ps))
  | P.Or ps -> (
      let ps = List.map simp ps in
      let ps = List.concat_map (function P.Or qs -> qs | q -> [ q ]) ps in
      match P.smart_or ps with P.Or [ q ] -> q | q -> q)
  | P.Implies (a, b) -> (
      let a = simp a and b = simp b in
      match () with
      | _ when P.is_true a -> b
      | _ when P.is_false a || P.is_true b -> P.mk_true
      | _ when P.is_false b -> P.mk_not a
      | _ -> P.Implies (a, b))
  | P.Iff (a, b) -> (
      let a = simp a and b = simp b in
      match () with
      | _ when P.equal_prop a b -> P.mk_true
      | _ when P.is_true a -> b
      | _ when P.is_false a -> P.mk_not b
      | _ when P.is_true b -> a
      | _ when P.is_false b -> P.mk_not a
      | _ -> P.Iff (a, b))
  | P.Ite (c, a, b) -> (
      let c = simp c and a = simp a and b = simp b in
      match () with
      | _ when P.is_true c -> a
      | _ when P.is_false c -> b
      | _ -> P.Ite (c, a, b))
  | P.Forall (u, q) -> P.Forall (u, simp q)
  | P.Exists (u, q) -> P.Exists (u, simp q)

(** canonical form for de-duplication: equalities are unordered *)
let rec canon (p : prop) =
  match (p, as_eq p) with
  | P.Not p, _ -> P.Not (canon p)
  | _, Some (a, b) ->
      let a, b = if P.compare_lit a.x b.x > 0 then (b, a) else (a, b) in
      P.Lit (P.AAppOp ((Op.BuiltinOp "==") #: Nt.Ty_unknown, [ a; b ]))
  | _, None -> p

let same_prop p1 p2 = P.equal_prop (canon p1) (canon p2)

(** Candidate definitions [x = t] read off a conjunct. *)
let definitions_of (p : prop) : (string * P.lit) list =
  let var_of (l : P.lit) = match l with P.AVar x -> Some x | _ -> None in
  match p with
  | P.Lit (P.AVar x) -> [ (x, P.mk_lit_true) ]
  | P.Not (P.Lit (P.AVar x)) -> [ (x, P.mk_lit_false) ]
  | P.Iff (P.Lit (P.AVar x), P.Lit l) | P.Iff (P.Lit l, P.Lit (P.AVar x)) ->
      [ (x, l) ]
  | _ -> (
      match as_eq p with
      | Some (a, b) ->
          (match var_of a.x with Some x -> [ (x, b.x) ] | None -> [])
          @ (match var_of b.x with Some y -> [ (y, a.x) ] | None -> [])
      | None -> [])

(** [exists u. (u = t /\ phi)] is [phi[t/u]] *)
let rec elim_exists (p : prop) : prop =
  match p with
  | P.Exists (u, body) -> (
      let body = elim_exists body in
      if not (List.mem u.x (P.fv_prop body)) then body
      else
        let cs = conjuncts body in
        let def =
          List.find_map
            (fun c ->
              match
                List.find_opt
                  (fun (x, t) ->
                    String.equal x u.x && not (List.mem u.x (P.fv_lit t)))
                  (definitions_of c)
              with
              | Some (_, t) -> Some (c, t)
              | None -> None)
            cs
        in
        match def with
        | Some (c, t) ->
            let rest = List.filter (fun c' -> c' != c) cs in
            elim_exists (P.subst_prop (u.x, t) (mk_conj rest))
        | None -> P.Exists (u, body))
  | P.And ps -> mk_conj (List.map elim_exists ps)
  | P.Or ps -> P.smart_or (List.map elim_exists ps)
  | P.Not p -> P.mk_not (elim_exists p)
  | P.Implies (a, b) -> P.Implies (elim_exists a, elim_exists b)
  | P.Iff (a, b) -> P.Iff (elim_exists a, elim_exists b)
  | P.Ite (a, b, c) -> P.Ite (elim_exists a, elim_exists b, elim_exists c)
  | P.Forall (u, body) -> P.Forall (u, elim_exists body)
  | P.Lit _ -> p

let clean p = simp (elim_exists (simp p))

(** Replace the Boolean atom [x] by the proposition [q]. *)
let rec subst_atom x q (p : prop) : prop =
  let f = subst_atom x q in
  match p with
  | P.Lit (P.AVar y) when String.equal x y -> q
  | P.Lit _ -> p
  | P.Not p -> P.Not (f p)
  | P.And ps -> P.And (List.map f ps)
  | P.Or ps -> P.Or (List.map f ps)
  | P.Implies (a, b) -> P.Implies (f a, f b)
  | P.Iff (a, b) -> P.Iff (f a, f b)
  | P.Ite (a, b, c) -> P.Ite (f a, f b, f c)
  | P.Forall (u, b) -> if String.equal u.x x then p else P.Forall (u, f b)
  | P.Exists (u, b) -> if String.equal u.x x then p else P.Exists (u, f b)

(* ------------------------------------------------------------------------ *)
(* Events of the concrete input trace                                        *)

let ev_vars (ev : eff_event) = List.map (fun x -> x.x) (ev.v :: ev.vs)

(** Split an event's qualifier into its own constraints and the pure
    constraints it carries, which hold of the valuation rather than of the
    event and can be lifted out of the trace test (the trace test is a plain
    concatenation of events).  An argument fixed by an equality is resolved
    first, so that constraints between it and the valuation become pure. *)
let normalize_event (ev : eff_event) : eff_event * prop list =
  let evars = ev_vars ev in
  let closed t = List.for_all (fun x -> not (List.mem x evars)) (P.fv_lit t) in
  let cs = conjuncts (clean ev.phi) in
  let defs =
    List.filter_map
      (fun c ->
        match
          List.find_opt
            (fun (x, t) -> List.mem x evars && closed t)
            (definitions_of c)
        with
        | Some (x, t) -> Some (x, t, c)
        | None -> None)
      cs
  in
  (* one definition per event variable *)
  let defs =
    List.fold_left
      (fun acc (x, t, c) ->
        if List.exists (fun (y, _, _) -> String.equal x y) acc then acc
        else acc @ [ (x, t, c) ])
      [] defs
  in
  let rest =
    List.filter (fun c -> not (List.exists (fun (_, _, c') -> c == c') defs)) cs
  in
  let rest =
    List.map
      (fun c ->
        clean @@ List.fold_left (fun c (x, t, _) -> P.subst_prop (x, t) c) c defs)
      rest
  in
  let own, pure =
    List.partition
      (fun c -> List.exists (fun x -> List.mem x evars) (P.fv_prop c))
      (List.concat_map conjuncts rest)
  in
  let own_defs = List.map (fun (_, _, c) -> c) defs in
  ({ ev with phi = mk_conj (own_defs @ own) }, pure)

(* ------------------------------------------------------------------------ *)
(* Reading the inference result                                              *)

let rec split_params (rty : rty) : string rtyped list * monad =
  match rty with
  | ArrRty { arr = NormalArr rx; rethty = Rty rty } ->
      let ps, m = split_params rty in
      (rx :: ps, m)
  | ArrRty { arr = NormalArr rx; rethty = Monad m } -> ([ rx ], m)
  | ArrRty { arr = GhostArr _ | ArrArr _; _ } ->
      unsupported "ghost or higher-order parameter"
  | ArrRty { rethty = Htriple _ | Inter _; _ } ->
      unsupported "Hoare-triple or intersection result type"
  | BaseRty _ -> unsupported "the task is not a function"

let rec split_binds (eff : Eff.t) : string ctyped list * Eff.t =
  match eff with
  | Eff.Bind (cx, eff) ->
      let bs, body = split_binds eff in
      (cx :: bs, body)
  | _ -> ([], eff)

let rec flatten_seq (eff : Eff.t) : Eff.t list =
  match eff with
  | Eff.Seq (e1, e2) -> flatten_seq e1 @ flatten_seq e2
  | Eff.Atom Eff.Id -> []
  | e -> [ e ]

let rec flatten_seqA (r : regex) : regex list =
  match r with
  | SeqA (r1, r2) -> flatten_seqA r1 @ flatten_seqA r2
  | EpsilonA phi when P.is_true phi -> []
  | r -> [ r ]

(** The query's existential binders and the two components of its
    [Constrain]; [None] for a trivial ([()]) component. *)
let query_parts (query : rty) =
  let _, m = split_params query in
  let ghosts, body = split_binds m.eff in
  let nontrivial = function Eff.Atom Eff.Id -> None | e -> Some e in
  match body with
  | Eff.Constrain (pre, post) -> (ghosts, nontrivial pre, nontrivial post)
  | _ -> (ghosts, None, nontrivial body)

(* ------------------------------------------------------------------------ *)
(* Synthesis state                                                           *)

type kind = KParam | KRet | KGhost | KLocal

(** An assumption; [anchor] is the index of the call after which it was
    introduced (the call producing a value it tests), [-1] if none. *)
type assume = { p : prop; anchor : int }

type state = {
  params : string rtyped list;
  ret_x : string;
  ret_cty : cty;
  ghosts : havoc list;
  locals : havoc list;
  assumes : assume list;
  trace : regex list;
  calls : Sft.ev list;
  pre : Eff.t option;
  post : Eff.t option;
  anchor_of : (string * int) list;  (** call-bound variable -> call index *)
}

let param_names st = List.map (fun rx -> rx.rx) st.params

let map_call f (ev : Sft.ev) : Sft.ev =
  let g (l : P.lit typed) = { l with x = f l.x } in
  { ev with args = List.map g ev.args; ret = g ev.ret }

let fv_call (ev : Sft.ev) =
  List.concat_map (fun (l : P.lit typed) -> P.fv_lit l.x) (ev.ret :: ev.args)

let havoc_fact h = conjuncts (P.subst_prop_id (v_name, h.hx) h.hphi)

let cty_fact x (cty : cty) = conjuncts (P.subst_prop_id (cty.v.x, x) cty.phi)

(** facts already stated by the binders, parameters and return type *)
let stated_facts st =
  List.concat_map havoc_fact (st.ghosts @ st.locals)
  @ List.concat_map
      (fun { rx; rty } ->
        match rty with BaseRty { cty } -> cty_fact rx cty | ArrRty _ -> [])
      st.params
  @ cty_fact st.ret_x st.ret_cty

let anchor_of_vars st xs =
  List.fold_left
    (fun a x ->
      match List.assoc_opt x st.anchor_of with Some i -> max a i | None -> a)
    (-1) xs

let normalize st =
  let ch h = { h with hphi = mk_conj (List.map clean (conjuncts h.hphi)) } in
  let st =
    {
      st with
      ghosts = List.map ch st.ghosts;
      locals = List.map ch st.locals;
      ret_cty = { st.ret_cty with phi = clean st.ret_cty.phi };
      calls = List.map (map_call fold_lit) st.calls;
    }
  in
  let facts = stated_facts st in
  let assumes =
    List.fold_left
      (fun acc a ->
        List.fold_left
          (fun acc p ->
            match List.find_opt (fun a' -> same_prop a'.p p) acc with
            | Some _ -> acc
            | None when P.is_true p || List.exists (same_prop p) facts -> acc
            | None -> acc @ [ { a with p } ])
          acc
          (conjuncts (clean a.p)))
      [] st.assumes
  in
  { st with assumes }

let subst_state (y, t) st =
  let sp = P.subst_prop (y, t) in
  let sh h = { h with hphi = sp h.hphi } in
  {
    st with
    ghosts = List.map sh st.ghosts;
    locals = List.map sh st.locals;
    assumes = List.map (fun a -> { a with p = sp a.p }) st.assumes;
    trace = List.map (SRL.subst (y, t)) st.trace;
    calls = List.map (map_call (P.subst_lit (y, t))) st.calls;
    pre = Option.map (subst_eff (y, t)) st.pre;
    post = Option.map (subst_eff (y, t)) st.post;
  }

let kind_of st x =
  if List.mem x (param_names st) then (KParam, 0)
  else if String.equal x st.ret_x then (KRet, 0)
  else
    match List.find_index (fun h -> String.equal h.hx x) st.ghosts with
    | Some i -> (KGhost, i)
    | None -> (
        match List.find_index (fun h -> String.equal h.hx x) st.locals with
        | Some i -> (KLocal, i)
        | None -> (KParam, 0) (* free in the context: keep *))

(** Lower rank is eliminated first: later locals, then later ghosts. *)
let rank st x =
  match kind_of st x with
  | KLocal, i -> (0, -i)
  | KGhost, i -> (1, -i)
  | KRet, _ -> (2, 0)
  | KParam, _ -> (3, 0)

let occurs st x =
  List.mem x
    (List.concat_map (fun a -> P.fv_prop a.p) st.assumes
    @ List.concat_map (fun h -> P.fv_prop h.hphi) (st.ghosts @ st.locals)
    @ List.concat_map fv_call st.calls
    @ List.concat_map SRL.fv st.trace
    @ List.concat_map fv_eff (Option.to_list st.pre @ Option.to_list st.post))

(** An elimination [x := t] is admissible when [x] is an existential of the
    witness and does not occur in [t], or when [x] is the return value, still
    occurs in the effect, and [t] mentions parameters only. *)
let admissible st (x, t) =
  (not (List.mem x (P.fv_lit t)))
  &&
  match kind_of st x with
  | (KLocal | KGhost), _ -> true
  | KRet, _ ->
      occurs st x
      && List.for_all (fun y -> List.mem y (param_names st)) (P.fv_lit t)
  | KParam, _ -> false

let by_rank st (x1, _) (x2, _) = Stdlib.compare (rank st x1) (rank st x2)

let pick_elimination st =
  let cands =
    List.concat_map
      (fun c ->
        match List.sort (by_rank st) (List.filter (admissible st) (definitions_of c)) with
        | [] -> []
        | d :: _ -> [ d ])
      (List.map (fun a -> a.p) st.assumes
      @ List.concat_map havoc_fact (st.ghosts @ st.locals)
      @ cty_fact st.ret_x st.ret_cty)
  in
  match List.sort (by_rank st) cands with [] -> None | d :: _ -> Some d

let eliminate st (x, t) =
  match kind_of st x with
  | KRet, _ ->
      let v = Nt.{ x = v_name; ty = st.ret_cty.v.ty } in
      let def = mk_prop_var_eq_lit v t in
      let cs = conjuncts st.ret_cty.phi in
      let cs = if List.exists (same_prop def) cs then cs else cs @ [ def ] in
      subst_state (x, t) { st with ret_cty = { st.ret_cty with phi = mk_conj cs } }
  | _ ->
      let h = List.find (fun h -> String.equal h.hx x) (st.ghosts @ st.locals) in
      let drop = List.filter (fun h' -> not (String.equal h'.hx x)) in
      let st =
        {
          st with
          ghosts = drop st.ghosts;
          locals = drop st.locals;
          assumes =
            st.assumes
            @ List.map
                (fun p ->
                  { p; anchor = anchor_of_vars st ((x :: P.fv_lit t) @ P.fv_prop p) })
                (conjuncts (P.subst_prop (v_name, t) h.hphi));
        }
      in
      subst_state (x, t) st

(** A local Boolean defined by [iff v q] is replaced by [q], provided it only
    occurs as a proposition. *)
let pick_bool_definition st =
  List.find_map
    (fun h ->
      match (h.hty, h.hphi) with
      | Nt.Ty_bool, (P.Iff (P.Lit (P.AVar v), q) | P.Iff (q, P.Lit (P.AVar v)))
        when String.equal v v_name
             && not (List.exists (fun y -> String.equal y v_name || String.equal y h.hx) (P.fv_prop q))
        ->
          let in_terms =
            List.mem h.hx
              (List.concat_map fv_call st.calls
              @ List.concat_map SRL.fv st.trace
              @ List.concat_map fv_eff (Option.to_list st.pre @ Option.to_list st.post))
          in
          let props =
            List.map (fun a -> a.p) st.assumes
            @ List.map (fun h' -> h'.hphi) (st.ghosts @ st.locals)
          in
          if
            in_terms
            || List.exists
                 (fun p -> List.mem h.hx (P.fv_prop (subst_atom h.hx q p)))
                 props
          then None
          else Some (h, q)
      | _ -> None)
    st.locals

let eliminate_bool st (h, q) =
  let sa = subst_atom h.hx q in
  let sh h' = { h' with hphi = sa h'.hphi } in
  {
    st with
    ghosts = List.map sh st.ghosts;
    locals = List.map sh (List.filter (fun h' -> h' != h) st.locals);
    assumes = List.map (fun a -> { a with p = sa a.p }) st.assumes;
  }

let rec skolemize st =
  let st = normalize st in
  match pick_elimination st with
  | Some d -> skolemize (eliminate st d)
  | None -> (
      match pick_bool_definition st with
      | Some d -> skolemize (eliminate_bool st d)
      | None -> st)

(* ------------------------------------------------------------------------ *)
(* Library calls that do not change the trace                               *)

(** An effect that only tests the trace: every transition of its SFTs echoes
    the event it reads and appends nothing (Admit), as opposed to Reject
    (deletes an event) and Append. *)
let rec preserves_trace opctx (e : Eff.t) =
  match e with
  | Eff.Atom Eff.Id | Eff.Guard _ | Eff.Atom (Eff.Trans (Trans.Admit _)) -> true
  | Eff.Atom (Eff.Trans (Trans.Explicit sft)) ->
      Sft.G.fold_edges_e
        (fun edge ok ->
          ok
          &&
          match Sft.G.E.label edge with
          | Sft.Label.Pred (_, [ Sft.IdentityF ]) | Sft.Label.Epsilon (_, []) -> true
          | Sft.Label.Pred _ | Sft.Label.Epsilon _ -> false)
        sft.g true
  | Eff.Atom (Eff.Trans (Trans.Append _ | Trans.Reject _)) | Eff.Constrain _ ->
      false
  | Eff.Atom (Eff.Call ev) -> call_preserves_trace opctx ev
  | Eff.Seq (e1, e2) | Eff.Choice (e1, e2) ->
      preserves_trace opctx e1 && preserves_trace opctx e2
  | Eff.Bind (_, e) -> preserves_trace opctx e

and call_preserves_trace opctx (ev : Sft.ev) =
  let rec spec = function
    | ArrRty { rethty = Rty rty; _ } -> spec rty
    | ArrRty { rethty = Monad m; _ } -> preserves_trace opctx m.eff
    | ArrRty _ -> false
    | BaseRty _ -> true
  in
  match ROpTypectx.get_ty_opt opctx (Op.EffOp ev.op) with
  | Some rty -> spec rty
  | None -> false

let mk_seqs (es : Eff.t list) : Eff.t =
  match List.rev es with
  | [] -> Eff.Atom Eff.Id
  | e :: rest -> List.fold_left (fun acc e' -> Eff.Seq (e', acc)) e rest

(** The presumption: the may-tests of the trace before the application.

    The rules give the residual query at the function entry as the query for
    the computation before it, [Tall ; DOM(exists r:t. FT)], where [FT] is
    the witness of the rest of the body composed with the query (Rules
    QLetExpFO and QLetAppFOFO, through JoinEffFO at the return).  Read
    declaratively, [DOM(exists r:t. FT)] is the may-test of "the path, then
    the query continuation at the returned value".  Calls that only test the
    trace are left out of it, since the path itself performs them on the same
    traces; what remains are the calls that change the trace, followed by
    the query.  Because a library call is a partial function on traces once
    its arguments and result are fixed, [path; reach k v] equals
    [reach (fun () -> path; k v) (); path], the presumption-first form of the
    paper's witnesses.

    The implementation's queries also test the incoming trace
    ([Constrain (pre, post)]); [pre] is part of the presumption, merged with
    the residual when it only tests the trace. *)
let presumptions opctx (st : state) : Eff.t list =
  let changes =
    List.filter (fun ev -> not (call_preserves_trace opctx ev)) st.calls
  in
  let residual =
    match st.post with
    | None -> []
    | Some post -> List.map (fun ev -> Eff.Atom (Eff.Call ev)) changes @ [ post ]
  in
  match st.pre with
  | Some pre when preserves_trace opctx pre -> [ mk_seqs (pre :: residual) ]
  | Some pre -> pre :: (if residual = [] then [] else [ mk_seqs residual ])
  | None -> if residual = [] then [] else [ mk_seqs residual ]

(* ------------------------------------------------------------------------ *)
(* Conditions on the inputs                                                  *)

let ctx_of_params (params : string rtyped list) : RTypectx.ctx =
  List.fold_left RTypectx.new_to_right RTypectx.empty params

(** [Gamma |-NV {v:b | phi}] (Rule NVBase): [phi] holds of some [v] in every
    valuation of [Gamma]. *)
let non_vacuous ctx (cty : cty) =
  Subtyping.is_bot_cty ctx
    (Cty.mk_unit_from_prop (P.mk_not (P.Exists (cty.v, cty.phi))))

(** An assumption about the parameters only becomes a refinement of the last
    parameter it mentions, as in the paper's witnesses ([xs:{v <> nil}],
    [ys:{v <> xs}]): Rule RNarrowPure narrows the query's argument type and
    Rule RSubEff then drops the filter that holds in every valuation
    (Example ex:match-false).  The narrowed argument type must stay
    non-vacuous (Rule NVBase); otherwise the assumption stays a filter. *)
let narrow_params st =
  let names () = List.map (fun rx -> rx.rx) st.params in
  let params = ref st.params in
  let assumes =
    List.filter
      (fun a ->
        let fvs = P.fv_prop a.p in
        let pnames = names () in
        if fvs = [] || not (List.for_all (fun y -> List.mem y pnames) fvs) then
          true
        else
          let k =
            List.fold_left
              (fun k y ->
                match List.find_index (String.equal y) pnames with
                | Some i -> max k i
                | None -> k)
              0 fvs
          in
          let rx = List.nth !params k in
          match rx.rty with
          | BaseRty { cty } ->
              let cty' =
                {
                  cty with
                  phi =
                    mk_conj
                      (conjuncts cty.phi
                      @ [ P.subst_prop_id (rx.rx, cty.v.x) a.p ]);
                }
              in
              let earlier = List.filteri (fun i _ -> i < k) !params in
              if non_vacuous (ctx_of_params earlier) cty' then (
                params :=
                  List.mapi
                    (fun i rx' ->
                      if i = k then { rx' with rty = BaseRty { cty = cty' } }
                      else rx')
                    !params;
                false)
              else true
          | ArrRty _ -> true)
      st.assumes
  in
  { st with params = !params; assumes }

(** A local that nothing but assumptions mentions, and whose constraints are
    satisfiable whatever the other variables are, claims nothing: drop it
    (Rule RSubEff in both directions). *)
let rec drop_implied st =
  let used =
    List.concat_map fv_call st.calls
    @ List.concat_map fv_eff (Option.to_list st.pre @ Option.to_list st.post)
    @ List.concat_map (fun h -> P.fv_prop h.hphi) (st.ghosts @ st.locals)
    @ P.fv_prop st.ret_cty.phi
  in
  let candidate =
    List.find_opt
      (fun h ->
        (not (List.mem h.hx used))
        &&
        let mine, _ =
          List.partition (fun a -> List.mem h.hx (P.fv_prop a.p)) st.assumes
        in
        let others = List.filter (fun h' -> h' != h) (st.ghosts @ st.locals) in
        let ctx =
          List.fold_left RTypectx.new_to_right (ctx_of_params st.params)
            (List.map
               (fun h' ->
                 {
                   rx = h'.hx;
                   rty =
                     BaseRty
                       { cty = { v = Nt.{ x = v_name; ty = h'.hty }; phi = h'.hphi } };
                 })
               others)
        in
        let v = Nt.{ x = h.hx; ty = h.hty } in
        let phi = mk_conj (havoc_fact h @ List.map (fun a -> a.p) mine) in
        non_vacuous ctx { v; phi })
      st.locals
  in
  match candidate with
  | None -> st
  | Some h ->
      drop_implied
        {
          st with
          locals = List.filter (fun h' -> h' != h) st.locals;
          assumes =
            List.filter (fun a -> not (List.mem h.hx (P.fv_prop a.p))) st.assumes;
        }

(* ------------------------------------------------------------------------ *)
(* Placement                                                                 *)

(** Lay the witness out as in the paper: the query's binders, the
    presumption (tests of the trace before the call), then the trace the
    application produces, i.e. the calls in program order.  A call binds its
    result right before it; any other binder goes to the earliest point
    where the variables of its refinement are bound; an assumption goes to
    the earliest point where its variables are bound and after the call that
    introduced it, except that an assumption about the return value goes
    last. *)
let place st (presume : Eff.t list) : step list =
  let bound = Hashtbl.create 16 in
  List.iter (fun x -> Hashtbl.replace bound x ()) (st.ret_x :: param_names st);
  let is_bound x = Hashtbl.mem bound x in
  let out = ref [] in
  let emit s = out := s :: !out in
  let ncalls = ref 0 in
  let pending_h = ref st.locals in
  let pending_a = ref st.assumes in
  let call_bound =
    List.filter_map
      (fun (ev : Sft.ev) -> match ev.ret.x with P.AVar x -> Some x | _ -> None)
      st.calls
  in
  let deps_of_h h =
    List.filter (fun y -> not (String.equal y v_name)) (P.fv_prop h.hphi)
  in
  let rec need x =
    if not (is_bound x) then (
      Hashtbl.replace bound x ();
      match List.find_opt (fun h -> String.equal h.hx x) !pending_h with
      | Some h ->
          pending_h := List.filter (fun h' -> h' != h) !pending_h;
          List.iter need (deps_of_h h);
          emit (Havoc h)
      | None -> () (* free: from the context *))
  in
  let lazy_havoc y =
    List.exists
      (fun h ->
        String.equal h.hx y && (not (List.mem y call_bound)) && P.is_true h.hphi)
      !pending_h
  in
  let mentions_ret p = List.mem st.ret_x (P.fv_prop p) in
  let rec flush () =
    let progress = ref false in
    List.iter
      (fun h ->
        if
          (not (List.mem h.hx call_bound))
          && (not (P.is_true h.hphi))
          && List.for_all is_bound (deps_of_h h)
        then (
          need h.hx;
          progress := true))
      !pending_h;
    let ready, rest =
      List.partition
        (fun a ->
          (not (mentions_ret a.p))
          && a.anchor < !ncalls
          && List.for_all (fun y -> is_bound y || lazy_havoc y) (P.fv_prop a.p))
        !pending_a
    in
    pending_a := rest;
    if ready <> [] then (
      List.iter (fun a -> List.iter need (P.fv_prop a.p)) ready;
      emit (Assume (mk_conj (List.map (fun a -> a.p) ready)));
      progress := true);
    if !progress then flush ()
  in
  List.iter
    (fun h ->
      Hashtbl.replace bound h.hx ();
      emit (Havoc h))
    st.ghosts;
  flush ();
  List.iter
    (fun k ->
      List.iter need (fv_eff k);
      flush ();
      emit (Presume k);
      flush ())
    presume;
  List.iter
    (fun ev ->
      List.iter need (fv_call ev);
      flush ();
      emit (Call ev);
      incr ncalls;
      flush ())
    st.calls;
  List.iter (fun h -> need h.hx) !pending_h;
  ncalls := max_int;
  flush ();
  if !pending_a <> [] then
    emit (Assume (mk_conj (List.map (fun a -> a.p) !pending_a)));
  List.rev !out

(* ------------------------------------------------------------------------ *)
(* Synthesis                                                                 *)

(** [infer_eff] names the program's return value [ret]; the joined result
    type keeps the query's name for it, which may differ (e.g. [res]). *)
let inferred_ret_name = "ret"

let synthesize ~opctx ~name ~(query : rty) ~(result : rty) : t =
  let params, m = split_params result in
  let ret_x, ret_cty =
    match m.ret.rty with
    | BaseRty { cty } -> (m.ret.rx, cty)
    | ArrRty _ -> unsupported "higher-order result"
  in
  let qghosts, pre, post = query_parts query in
  let ghost_names = List.map (fun cx -> cx.cx) qghosts in
  let eff =
    if
      String.equal ret_x inferred_ret_name
      || List.mem inferred_ret_name
           (ghost_names @ List.map (fun rx -> rx.rx) params)
    then m.eff
    else subst_eff (inferred_ret_name, P.AVar ret_x) m.eff
  in
  let binders, body = split_binds eff in
  let atoms = flatten_seq body in
  let tests, calls =
    List.partition
      (function Eff.Atom (Eff.Trans (Trans.Admit _)) -> true | _ -> false)
      atoms
  in
  let trace_labels =
    match tests with
    | [] -> []
    | [ Eff.Atom (Eff.Trans (Trans.Admit r)) ] ->
        (* [Backwards.run] builds this regex from the path returned by
           [Sft.find_witness], which lists the last transition first *)
        List.rev (flatten_seqA r)
    | _ -> unsupported "more than one trace test"
  in
  let calls =
    List.map
      (function
        | Eff.Atom (Eff.Call ev) -> ev
        | e -> unsupported "unexpected step %s" (layout_eff e))
      calls
  in
  let anchor_of =
    List.rev
    @@ List.filter_map
         (fun (i, (ev : Sft.ev)) ->
           match ev.ret.x with P.AVar x -> Some (x, i) | _ -> None)
         (List.mapi (fun i ev -> (i, ev)) calls)
  in
  let trace, lifted =
    List.fold_left
      (fun (tr, lifted) r ->
        match r with
        | EpsilonA phi -> (tr, lifted @ conjuncts (clean phi))
        | EventA (EffEvent ev) ->
            let ev, pure = normalize_event ev in
            (tr @ [ EventA (EffEvent ev) ], lifted @ pure)
        | r -> (tr @ [ r ], lifted))
      ([], []) trace_labels
  in
  let ghosts, locals, path_assumes =
    List.fold_left
      (fun (gs, ls, asm) { cx; cty } ->
        match cty.v.ty with
        | Nt.Ty_unit -> (gs, ls, asm @ conjuncts cty.phi)
        | ty ->
            let h = { hx = cx; hty = ty; hphi = cty.phi } in
            if List.mem cx ghost_names then (gs @ [ h ], ls, asm)
            else (gs, ls @ [ h ], asm))
      ([], [], []) binders
  in
  let st =
    {
      params;
      ret_x;
      ret_cty;
      ghosts;
      locals;
      assumes = [];
      trace;
      calls;
      pre;
      post;
      anchor_of;
    }
  in
  (* conditions met along the path are placed after the call producing the
     values they test; those carried by the input trace are not anchored *)
  let assumes =
    List.map (fun p -> { p; anchor = anchor_of_vars st (P.fv_prop p) }) path_assumes
    @ List.map (fun p -> { p; anchor = -1 }) lifted
  in
  let st = skolemize { st with assumes } in
  let st = drop_implied (narrow_params st) in
  {
    name;
    params = st.params;
    ret = (st.ret_x, st.ret_cty);
    steps = place st (presumptions opctx st);
    found_trace = st.trace;
  }

(* ------------------------------------------------------------------------ *)
(* Printing in the surface syntax                                            *)

let one_line s =
  let b = Buffer.create (String.length s) in
  let last_space = ref false in
  String.iter
    (fun c ->
      match c with
      | '\n' | ' ' | '\t' ->
          if not !last_space then Buffer.add_char b ' ';
          last_space := true
      | c ->
          Buffer.add_char b c;
          last_space := false)
    s;
  String.trim (Buffer.contents b)

let pp_prop p =
  one_line @@ Ocaml5_parser.Pprintast.string_of_expression
  @@ To_qualifier.qualifier_to_ocamlexpr (Coersion.Qualifier.besome p)

let pp_lit l =
  one_line @@ Ocaml5_parser.Pprintast.string_of_expression
  @@ To_lit.lit_to_ocamlexpr (Coersion.Lit.besome l)

let paren s =
  let atomic =
    String.equal s "()"
    || String.for_all
         (fun c ->
           match c with
           | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' | '.' -> true
           | _ -> false)
         s
  in
  if atomic then s else spf "(%s)" s

let pp_cty ty phi = spf "(%s : [%%v: %s])" (pp_prop phi) (Nt.layout ty)
let pp_op op = String.capitalize_ascii op

let pp_call (ev : Sft.ev) =
  spf "%s (%s)" (pp_op ev.op)
    (String.concat ", "
       (List.map (fun (l : P.lit typed) -> pp_lit l.x) (ev.args @ [ ev.ret ])))

(** [Op (a1, ..., an, r, phi)]; an argument that [phi] equates to a variable
    [y] is written [(y [@d])], the sugar of [libRty] specifications (which
    only admits variables) *)
let rec pp_event (ev : eff_event) =
  (* The SFT names event variables [x_0, x_1, ...] and [vret]; the parser's
     [@d] sugar introduces fresh names of the same shape, so rename them. *)
  let outer = Rty.SRL.SE.fv_eff_event ev in
  let rec fresh base = if List.mem base outer then fresh (base ^ "'") else base in
  let renaming =
    List.mapi (fun i (x : string typed) -> (x.x, fresh (spf "a%i" i))) ev.vs
    @ [ (ev.v.x, fresh "u") ]
  in
  let targets = List.map snd renaming in
  if List.exists (fun (x, _) -> List.mem x targets) renaming then pp_event_ ev
  else
    let phi =
      List.fold_left (fun p (x, y) -> P.subst_prop_id (x, y) p) ev.phi renaming
    in
    let rn (x : string typed) = { x with x = List.assoc x.x renaming } in
    pp_event_ { ev with vs = List.map rn ev.vs; v = rn ev.v; phi }

and pp_event_ (ev : eff_event) =
  let cs = conjuncts ev.phi in
  let evars = ev_vars ev in
  let closed t =
    (match t with P.AVar _ -> true | _ -> false)
    && List.for_all (fun x -> not (List.mem x evars)) (P.fv_lit t)
  in
  let used = ref [] in
  let def_of (x : string typed) =
    List.find_map
      (fun c ->
        if List.memq c !used then None
        else
          match
            List.find_opt
              (fun (y, t) -> String.equal x.x y && closed t)
              (definitions_of c)
          with
          | Some (_, t) -> Some (c, t)
          | None -> None)
      cs
  in
  let arg (x : string typed) =
    match def_of x with
    | Some (c, t) ->
        used := c :: !used;
        spf "(%s [@d])" (pp_lit t)
    | None -> x.x
  in
  (* The parser renames event variables positionally after desugaring [@d];
     mixing [@d] with named arguments can capture, so sugar all or none of
     the arguments. *)
  let sugar = List.for_all (fun x -> Option.is_some (def_of x)) ev.vs in
  let args =
    if sugar then List.map arg (ev.vs @ [ ev.v ])
    else List.map (fun (x : string typed) -> x.x) (ev.vs @ [ ev.v ])
  in
  let rest = List.filter (fun c -> not (List.memq c !used)) cs in
  spf "%s (%s)" (pp_op ev.op) (String.concat ", " (args @ [ pp_prop (mk_conj rest) ]))

let rec pp_regex (r : regex) =
  match r with
  | EmptyA -> "emptyA"
  | AnyA -> "anyA"
  | EpsilonA phi when P.is_true phi -> "epsilonA"
  | EpsilonA phi -> unsupported "guarded epsilon %s inside a trace" (pp_prop phi)
  | EventA (EffEvent ev) -> pp_event ev
  | EventA (GuardEvent phi) -> spf "Any (%s)" (pp_prop phi)
  | LorA (a, b) -> spf "(%s || %s)" (pp_regex a) (pp_regex b)
  | LandA (a, b) -> spf "(%s && %s)" (pp_regex a) (pp_regex b)
  | SetMinusA (a, b) -> spf "(%s - %s)" (pp_regex a) (pp_regex b)
  | SeqA (a, b) -> spf "(%s; %s)" (pp_regex a) (pp_regex b)
  | StarA a -> spf "starA %s" (paren (pp_regex a))
  | ComplementA a -> spf "not %s" (paren (pp_regex a))

let pp_regexes = function
  | [] -> "epsilonA"
  | [ r ] -> pp_regex r
  | rs -> spf "(%s)" (String.concat "; " (List.map pp_regex rs))

(** surface syntax of the effects users write in queries *)
let rec pp_eff (e : Eff.t) =
  match e with
  | Eff.Atom Eff.Id -> "()"
  | Eff.Atom (Eff.Call ev) -> pp_call ev
  | Eff.Atom (Eff.Trans (Trans.Admit r)) -> spf "Admit %s" (paren (pp_regex r))
  | Eff.Atom (Eff.Trans (Trans.Append ev)) -> spf "Append %s" (paren (pp_call ev))
  | Eff.Atom (Eff.Trans (Trans.Reject _ | Trans.Explicit _)) ->
      unsupported "transducer in a query effect"
  | Eff.Guard phi -> spf "Guard %s" (paren (pp_prop phi))
  | Eff.Seq (e1, e2) -> spf "%s; %s" (pp_eff e1) (pp_eff e2)
  | Eff.Choice (e1, e2) -> spf "Choice (%s, %s)" (pp_eff e1) (pp_eff e2)
  | Eff.Bind ({ cx; cty }, e) ->
      spf "let (%s : %s) = %s in %s" cx (Nt.layout cty.v.ty)
        (pp_cty cty.v.ty cty.phi) (pp_eff e)
  | Eff.Constrain (e1, e2) -> spf "Constrain (%s, %s)" (pp_eff e1) (pp_eff e2)

let pp_step = function
  | Havoc h ->
      `Let (spf "let (%s : %s) = %s in" h.hx (Nt.layout h.hty) (pp_cty h.hty h.hphi))
  | Assume p -> `Do (spf "Guard %s" (paren (pp_prop p)))
  | Call ev -> `Do (pp_call ev)
  | Presume k -> `Do (spf "Reach (fun () -> %s) ()" (pp_eff k))

(** an event of a trace, in the notation of the paper's traces *)
let pp_trace_event (r : regex) =
  match r with
  | EventA (EffEvent ev) ->
      let cs = conjuncts ev.phi in
      let evars = ev_vars ev in
      let used = ref [] in
      let value (x : string typed) =
        match
          List.find_map
            (fun c ->
              if List.memq c !used then None
              else
                match
                  List.find_opt
                    (fun (y, t) ->
                      String.equal x.x y
                      && List.for_all (fun z -> not (List.mem z evars)) (P.fv_lit t))
                    (definitions_of c)
                with
                | Some (_, t) ->
                    used := c :: !used;
                    Some t
                | None -> None)
            cs
        with
        | Some t -> paren (pp_lit t)
        | None -> x.x
      in
      let args = List.map value ev.vs in
      let ret =
        match ev.v.ty with Nt.Ty_unit -> "" | _ -> " = " ^ value ev.v
      in
      let rest = List.filter (fun c -> not (List.memq c !used)) cs in
      spf "<%s%s%s%s>" ev.op
        (String.concat "" (List.map (fun a -> " " ^ a) args))
        ret
        (if rest = [] then "" else " | " ^ pp_prop (mk_conj rest))
  | r -> pp_regex r

let layout (w : t) =
  let params =
    String.concat " "
      (List.map
         (fun { rx; rty } ->
           match rty with
           | BaseRty { cty } -> spf "?l:(%s = %s)" rx (pp_cty cty.v.ty cty.phi)
           | ArrRty _ -> unsupported "higher-order parameter")
         w.params)
  in
  let ret_x, ret_cty = w.ret in
  let lines = List.map pp_step w.steps in
  let n = List.length lines in
  let body =
    List.mapi
      (fun i l ->
        let last = i = n - 1 in
        let pre = if i = 0 then "(" else " " in
        match l with
        | `Let s -> spf "      %s%s%s" pre s (if last then " ())" else "")
        | `Do s -> spf "      %s%s%s" pre s (if last then ")" else ";"))
      lines
  in
  let body = if n = 0 then [ "      ()" ] else body in
  String.concat "\n"
    ([
       spf "let[@witnessRty] %s %s =" w.name params;
       "  {";
       spf "    %s = %s;" ret_x (pp_cty ret_cty.v.ty ret_cty.phi);
       "    eff =";
     ]
    @ body @ [ "  }" ]
    @
    if w.found_trace = [] then []
    else
      [
        spf "(* an incoming trace satisfying the presumption, found by the search: [%s] *)"
          (String.concat "; " (List.map pp_trace_event w.found_trace));
      ])

(** Witness of a successful task, or the reason it cannot be printed. *)
let render ~opctx ~name ~query ~result =
  try Ok (layout (synthesize ~opctx ~name ~query ~result)) with
  | Unsupported msg -> Error msg
  | e -> Error (Printexc.to_string e)
