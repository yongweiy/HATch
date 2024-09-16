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
  end

  module Dot = Graph.Graphviz.Dot (G)

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

  let to_dot_file filename t =
    let oc = open_out filename in
    Dot.output_graph oc t.graph;
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

  let intersect a1 a2 = failwith "TODO"
end
