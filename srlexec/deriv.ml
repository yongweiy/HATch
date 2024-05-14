(** Left Quotient
    TODO: add flag to control direction of quotient for `admit`
 *)

open Zzdatatype.Datatype
open Language
open Sugar
open Rty
open Utils
module L = Literal
module C = Choice
module Tr = Trace

let rec is_nullable = function
  | EmptyA -> false
  | EpsilonA -> true
  | AnyA -> false
  | EventA (GuardEvent _) -> false
  | EventA (EffEvent _) -> false
  | LorA (r, s) -> is_nullable r || is_nullable s
  | LandA (r, s) -> is_nullable r && is_nullable s
  | SeqA (r, s) -> is_nullable r && is_nullable s
  | StarA _ -> true
  | ComplementA r -> not (is_nullable r)
  | SetMinusA (r, s) -> is_nullable r && not (is_nullable s)

let rec next_literal = function
  | EmptyA | EpsilonA -> []
  | AnyA -> [ L.mk_true ]
  | EventA sev -> [ L.of_sevent sev ]
  | LorA (r, s) -> L.join (next_literal r) (next_literal s)
  | LandA (r, s) ->
      List.cartesian_map L.mk_and (next_literal r) (next_literal s)
  | SeqA (r, s) when is_nullable r -> L.join (next_literal r) (next_literal s)
  | SeqA (r, s) -> next_literal r
  | StarA r -> next_literal r
  (* TODO: can we do better? pruning? ordering? *)
  | ComplementA r ->
      let lits = next_literal r in
      L.neg_literals lits :: lits
  | SetMinusA (AnyA, EventA sev) -> [ L.mk_not @@ L.of_sevent sev ]
  | SetMinusA (r, s) -> next_literal @@ LandA (r, ComplementA s)
(* _failatwith __FILE__ __LINE__ *)
(* @@ spf "next_literal: %s" @@ Rty.layout_regex r *)

let mk_complementA = function
  | EmptyA -> StarA AnyA
  | StarA AnyA -> EmptyA
  | r -> ComplementA r

let mk_orA r s =
  if r = EmptyA then s
  else if s = EmptyA then r
  else if r = StarA AnyA || s = StarA AnyA then StarA AnyA
  else if r = s then r
  else LorA (r, s)

let mk_andA r s =
  if r = EmptyA then EmptyA
  else if s = EmptyA then EmptyA
  else if r = StarA AnyA then s
  else if s = StarA AnyA then r
  else if (r = EpsilonA && is_nullable s) || (s = EpsilonA && is_nullable r)
  then EpsilonA
  else if r = s then r
  else match s with ComplementA s' when r = s' -> EmptyA | _ -> LandA (r, s)

let mk_seqA r s =
  if r = EpsilonA then s else if r = EmptyA then EmptyA else SeqA (r, s)

let quot l r =
  let rec aux = function
    | EmptyA | EpsilonA -> EmptyA
    | AnyA -> EpsilonA
    | EventA sev -> if L.entails_sevent l sev then EpsilonA else EmptyA
    | LorA (r, s) -> mk_orA (aux r) (aux s)
    | LandA (r, s) -> mk_andA (aux r) (aux s)
    | SeqA (r, s) when is_nullable r -> mk_orA (mk_seqA (aux r) s) (aux s)
    | SeqA (r, s) -> mk_seqA (aux r) s
    | StarA r -> mk_seqA (aux r) (StarA r)
    | ComplementA r -> mk_complementA (aux r)
    | SetMinusA (r, s) -> aux @@ LandA (r, ComplementA s)
  in
  (* TODO: see if simplify the result helps performance *)
  aux r

(* let symb_quot ~rctx ~gvars trace regex = *)
(*   List.fold_left *)
(*     (fun ress lit -> *)
(*       let* tr_rev, regex = ress in *)
(*       let+ lit', regex' = symb_deriv ~rctx ~gvars lit regex in *)
(*       (lit' :: tr_rev, regex')) *)
(*     (Choice.return ([], regex)) *)
(*     trace *)

(* let symb_match ?(rctx = []) ?(gvars = []) trace regex = *)
(*   symb_quot ~rctx ~gvars trace regex *)
(*   |> Choice.map (fun (_, r) -> is_nullable r) *)
(*   |> Choice.forall *)

module DerivGraph = struct
  include
    Graph.Imperative.Digraph.AbstractLabeled
      (struct
        type t = sfa
      end)
      (struct
        type t = L.literal [@@deriving compare, equal, hash]

        (** default edge label should never be used *)
        let default = L.mk_false
      end)

  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let default_edge_attributes _ = []

  module VCache = Hashtbl.Make (V)

  let vertex_name v = "S_" ^ string_of_int @@ V.hash v

  let vertex_attributes v =
    let r = V.label v in
    [
      `Label (Rty.layout_regex r);
      `Color (if is_nullable r then 0x00ee00 else 0x000000);
    ]

  let edge_attributes e = [ `Label (L.layout_literal @@ E.label e) ]
  let get_subgraph _ = None
end

module type FlagT = sig
  val flag : bool
end

module type IntT = sig
  val bound : int
end

module SFA (AllowEmpty : FlagT) (LookAhead : IntT) = struct
  open DerivGraph

  let g = create ()
  let fold_succ f d acc = fold_succ f g d acc
  let iter_succ f d = iter_succ f g d

  type deriv = V.t [@@deriving compare, equal]

  let set_dist = Mark.set

  let get_dist d =
    let dist = Mark.get d in
    if dist = max_int then None else Some dist

  (** update the distance of `d` and derivatives
      along the path to `empty` under `bound` *)
  let update_dist d =
    let rec aux len d =
      match get_dist d with
      | Some dist -> dist
      | None ->
          if len = LookAhead.bound then max_int
          else
            let dist =
              fold_succ (fun d' -> min @@ aux (len + 1) d') d max_int
            in
            set_dist d dist;
            dist
    in
    ignore (aux 0 d)

  module Table = Hashtbl.Make (struct
    type t = sfa [@@deriving compare, equal, hash]
  end)

  let to_deriv =
    let tbl = Table.create 10 in
    fun sfa ->
      match Table.find_opt tbl sfa with
      | Some d -> d
      | None ->
          let d = V.create sfa in
          set_dist d max_int;
          Table.add tbl sfa d;
          DerivGraph.add_vertex g d;
          d

  let of_deriv = V.label
  let layout_deriv = Rty.layout_regex << of_deriv
  let is_nullable d = is_nullable @@ of_deriv d
  let is_free d = SRL.equal_sfa (StarA AnyA) @@ of_deriv d

  (** syntactically check if a derivative is equivalent to empty *)
  let is_empty d =
    let r = of_deriv d in
    if SRL.equal_sfa r EmptyA then true
    else (
      _assert __FILE__ __LINE__ "Deriv.is_empty" @@ not @@ SRL.is_empty r;
      false)

  let empty = to_deriv EmptyA
  let () = set_dist empty 0

  let init sfa =
    let d = to_deriv sfa in
    add_vertex g d;
    d

  let new_trans d l d' = add_edge_e g @@ E.create d l d'
  let get_nexts d = List.map (fun e -> (E.label e, E.dst e)) @@ succ_e g d

  module Dot = Graph.Graphviz.Dot (DerivGraph)

  let output oc = Dot.output_graph oc g

  (** return the sibling states of the initial state of sfa `r`

    TODO: add a flag for prioritizing the sibling states closer to EmptyA
    , can be implemented via the `Mark` module
    TODO: add a flag for omitting `neg_literals` case
 *)
  let next ~substs d =
    C.of_list
    @@
    match get_nexts d with
    (* a state is explored if all neighbors are
       and unexplored if none of neighbors are *)
    | [] ->
        let lits =
          List.filter_map (L.notbot_opt ~substs) @@ next_literal @@ of_deriv d
        in
        let nexts =
          List.map (fun l -> (l, to_deriv @@ quot l @@ of_deriv d)) lits
        in
        let nexts =
          if LookAhead.bound > 0 then (
            List.iter (update_dist << snd) nexts;
            List.sort
              (fun (_, d) (_, d') -> Int.compare (Mark.get d) (Mark.get d'))
              nexts)
          else nexts
        in
        let nexts =
          if AllowEmpty.flag then (L.neg_literals lits, empty) :: nexts
          else nexts
        in
        List.iter (fun (l, d') -> new_trans d l d') nexts;
        nexts
    | trans -> trans

  let match_and_refine ~rctx ~substs l d =
    let^ l', d' = next ~substs d in
    let l'' = L.mk_and l l' in
    L.notbot_opt ~rctx ~substs l'' |> Option.map @@ fun l'' -> (l'', d')

  let match_and_refine_trace ~rctx ~substs tr d =
    Tr.fold
      (fun atom ->
        C.bind @@ fun (touchable, tr, d) ->
        match atom with
        | TamperSeal ->
            _assert __FILE__ __LINE__ "two Untouchable flag" @@ touchable;
            C.return (false, Tr.snoc TamperSeal tr, d)
        | _ when is_free d -> C.return (touchable, Tr.snoc atom tr, d)
        | Repeat _ -> C.fail (* TODO: UNIMP *)
        | Atom l ->
            let* () = C.guard touchable in
            let+ l', d' = match_and_refine ~rctx ~substs l d in
            (touchable, Tr.snoc (Atom l') tr, d'))
      tr
      (C.return (true, Tr.empty, d))

  (** enumerate all viable paths that start from the state
    denoted by `r` and are of length [`low`, `high`] *)
  let enum ~substs ~len_range:(low, high) d =
    let advance acc =
      let* tr, d = acc in
      let* l, d' = next ~substs d in
      C.return (Tr.snoc (Atom l) tr, d')
    in
    let rec bfs len acc res =
      if len > high then res
      else
        let res = if len >= low then C.(acc ++ res) else res in
        let acc' = advance acc in
        if C.is_empty acc' then res else bfs (len + 1) acc' res
    in
    bfs 0 (C.return (Tr.empty, d)) C.fail
end

module EffSFA =
  SFA
    (struct
      let flag = false
    end)
    (struct
      let bound = 0
    end)

module ContSFA =
  SFA
    (struct
      let flag = true
    end)
    (struct
      let bound = 1
    end)
