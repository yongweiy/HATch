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

let deriv l r =
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
    Graph.Imperative.Digraph.ConcreteLabeled
      (struct
        type t = sfa [@@deriving compare, equal, hash]
      end)
      (struct
        type t = L.literal [@@deriving compare, equal, hash]

        (* let compare _ _ = 0 *)

        (** default edge label should never be used *)
        let default = L.mk_false
      end)

  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let default_edge_attributes _ = []

  module VCache = Hashtbl.Make (V)

  let vertex_name =
    let count = ref 0 in
    let cache = VCache.create 11 in
    fun v ->
      match VCache.find_opt cache v with
      | Some name -> name
      | None ->
          let name = "S" ^ string_of_int !count in
          count := !count + 1;
          VCache.add cache v name;
          name

  let vertex_attributes r = [ `Label (Rty.layout_regex r) ]
  let edge_attributes e = [ `Label (L.layout_literal @@ E.label e) ]
  let get_subgraph _ = None
end

module G = struct
  open DerivGraph

  let g = create ()
  let () = add_vertex g EmptyA
  let init r = add_vertex g r
  let member = mem_vertex g

  let link r l s =
    _assert __FILE__ __LINE__ "die" @@ member r;
    (* _assert __FILE__ __LINE__ "die" @@ not @@ mem_edge g r s; *)
    add_edge_e g @@ E.create r l s

  let next r = List.map (fun e -> (E.label e, E.dst e)) @@ succ_e g r

  module Dot = Graph.Graphviz.Dot (DerivGraph)

  let output oc = Dot.output_graph oc g
end

(** return the sibling states of the initial state of sfa `r`

    TODO: add a flag for prioritizing the sibling states closer to EmptyA
    , can be implemented via the `Mark` module
 *)
let next ~substs r =
  C.of_list
  @@
  match G.next r with
  (* a state is explored if all neighbors are
     and unexplored if none of neighbors are *)
  | [] ->
      next_literal r
      |> List.filter_map @@ L.notbot_opt ~substs
      |> List.map (fun l ->
             let s = deriv l r in
             G.link r l s;
             (l, s))
  | trans -> trans

let match_and_refine ~rctx ~substs l r =
  let^ l', r' = next ~substs r in
  let l'' = L.mk_and l l' in
  L.notbot_opt ~rctx ~substs l'' |> Option.map @@ fun l'' -> (l'', r')

let match_and_refine_trace ~rctx ~substs tr r =
  Tr.fold_left
    (fun ress l ->
      let* tr, r = ress in
      let* l', r = match_and_refine ~rctx ~substs l r in
      C.return (Tr.snoc l' tr, r))
    (C.return (Tr.empty, r))
    tr

(** enumerate all paths that start from the state
    denoted by `r` and are of length [`low`, `high`] *)
let enum ~substs ~len_range:(low, high) r =
  let advance acc =
    let* tr, r = acc in
    let* l, r' = next ~substs r in
    C.return (Tr.snoc l tr, r')
  in
  let rec bfs len acc res =
    if len > high then res
    else
      let res = if len >= low then C.(acc ++ res) else res in
      let acc' = advance acc in
      if C.is_empty acc' then res else bfs (len + 1) acc' res
  in
  bfs 0 (C.return (Tr.empty, r)) C.fail
