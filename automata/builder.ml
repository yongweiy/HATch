open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin
open Zzdatatype.Datatype
open Sugar
open Language
open Rty

module F (L : Literal.T) = struct
  module G = struct
    include
      Graph.Persistent.Digraph.ConcreteLabeled
        (struct
          type t = regex list [@@deriving compare, equal, hash]
        end)
        (L)

    let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let default_edge_attributes _ = []
    let vertex_name v = "S_" ^ string_of_int @@ V.hash v
    let init = ref []
    let finals = ref []

    let vertex_attributes v =
      [
        `Label (List.to_string layout_regex v);
        `Color
          (if List.equal equal_regex v !init then 0x00eeff
           else if !finals |> List.exists @@ List.equal equal_regex v then
             0x00ee00
           else 0x000000);
      ]

    let edge_attributes e = [ `Label (L.layout @@ E.label e) ]
    let get_subgraph _ = None

    let inter (v1, g1) (v2, g2) =
      let rec aux v1 v2 g =
        let v = v1 @ v2 in
        if mem_vertex g v then g
        else
          fold_succ_e
            (fun (_, l1, u1) g ->
              fold_succ_e
                (fun (_, l2, u2) g ->
                  match L.(notbot_opt ~substs:[] @@ mk_and l1 l2) with
                  | Some l ->
                      add_edge_e (aux u1 u2 g) @@ E.create v l @@ u1 @ u2
                  | None -> g)
                g2 v2 g)
            g1 v1
          @@ add_vertex g v
      in
      aux v1 v2 empty
  end

  module Dot = Graph.Graphviz.Dot (G)
  module PathCheck = Graph.Path.Check (G)

  module EdgeMapper =
    Graph.Gmap.Edge
      (G)
      (struct
        include G
        include Graph.Builder.P (G)
      end)

  type t = { init : G.V.t; finals : G.V.t list; graph : G.t }

  let pp_print ppf { init; finals; graph } =
    let open Format in
    let pp_regex ppf r = pp_print_string ppf @@ layout_regex r in
    let pp_regexes ppf rs =
      pp_print_list
        ~pp_sep:(fun ppf () -> pp_print_string ppf ",")
        pp_regex ppf rs
    in
    fprintf ppf "@[<v 2>init:@ %a@ finals:@ %a@ graph:@ %a@]" pp_regexes init
      (pp_print_list pp_regexes) finals Dot.fprint_graph graph

  let to_dot_file filename { init; finals; graph } =
    let oc = open_out filename in
    G.init := init;
    G.finals := finals;
    Dot.output_graph oc graph;
    close_out oc

  let of_regex =
    let rec next = function
      | EmptyA | EpsilonA -> []
      | AnyA -> [ L.mk_top ]
      | EventA sev -> [ L.of_sevent sev ]
      | LorA (r, s) -> L.join (next r) (next s)
      | LandA (r, s) -> List.cartesian_map L.mk_and (next r) (next s)
      | SeqA (r, s) when is_nullable r -> L.join (next r) (next s)
      | SeqA (r, s) -> next r
      | StarA r -> next r
      | ComplementA r ->
          let lits = next r in
          (L.mk_not @@ L.mk_or_list lits) :: lits
      | SetMinusA (AnyA, EventA sev) -> [ L.mk_not @@ L.of_sevent sev ]
      | SetMinusA (r, s) -> next @@ mk_andA (r, mk_complementA s)
    in
    let rec aux r g =
      if G.mem_vertex g [ r ] then g
      else
        let () = Printf.printf "%s\n" @@ layout_regex r in
        let () = flush stdout in
        next r
        |> List.map (fun l -> (l, L.quotient l r))
        |> List.sort_and_combine
             (fun (_, r) (_, s) -> compare_regex r s)
             (fun (l_r, r) (l_s, s) -> (L.mk_or l_r l_s, r))
        |> List.fold_left
             (fun g (l, s) ->
               G.add_edge_e (aux s g) @@ G.E.create [ r ] l [ s ])
             (G.add_vertex g [ r ])
    in
    fun r ->
      let graph = aux r G.empty in
      let finals =
        G.fold_vertex
          (fun v acc -> if is_nullable @@ List.hd v then v :: acc else acc)
          graph []
      in
      { init = [ r ]; finals; graph }

  (** intersect two automaton structures *)
  let intersect a1 a2 =
    let graph = G.inter (a1.init, a1.graph) (a2.init, a2.graph) in
    let finals =
      List.fold_product
        (fun finals v1 v2 ->
          let v = v1 @ v2 in
          if G.mem_vertex graph v then v :: finals else finals)
        a1.finals a2.finals []
    in
    { init = a1.init @ a2.init; finals; graph }

  (** compute the quotient of [numerator] over [denominator] with
      [start_num] being the initial states; the result quotient is
      expressed as a disjunction between {i partial} quotients, which
      takes the form of a non-deterministic choice, as embedded in
      [Choice.t], among states in [numerator] that denote the initial
      state of the associated partial quotients, along with automata
      that witness the quotienting. *)
  let quotient (init_num, dist_to_finals, numerator) denominator =
    let size_num = List.length numerator.init in
    let init = init_num @ denominator.init in
    let graph =
      G.inter (init_num, numerator.graph) (denominator.init, denominator.graph)
    in
    let pathchecker = PathCheck.create graph in
    let finals =
      G.fold_vertex
        (fun v acc ->
          let v_den = List.drop size_num v in
          if List.mem ~eq:G.V.equal v_den denominator.finals then v :: acc
          else acc)
        graph []
      |> List.sort (fun v u ->
             Int.compare (dist_to_finals v) (dist_to_finals u))
    in
    let edge_filter final (v, l, u) =
      if
        PathCheck.check_path pathchecker v final
        && PathCheck.check_path pathchecker u final
      then Some (v, l, u)
      else None
    in
    finals |> Choice.of_list
    |> Choice.map @@ fun final ->
       let graph = EdgeMapper.filter_map (edge_filter final) graph in
       ({ init; finals = [ final ]; graph }, final)
end
