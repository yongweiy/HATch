open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin
open Zzdatatype.Datatype
open Sugar
open Sig

module F
    (Q : sig
      type t [@@deriving compare, equal, hash]

      val ( @ ) : t -> t -> t
    end)
    (L : EBA) =
struct
  open Q

  module G = struct
    include
      Graph.Persistent.Digraph.ConcreteLabeled
        (Q)
        (struct
          type t = L.pred [@@deriving compare]

          let default = L.mk_bot
        end)

    module VTbl = Hashtbl.Make (Q)

    let inter ?qinv ~is_bot (v1, g1) (v2, g2) =
      let record_state_comb =
        match qinv with Some qinv -> VTbl.add qinv | None -> fun _ _ -> ()
      in
      let rec aux v1 v2 g =
        let v = v1 @ v2 in
        if mem_vertex g v then g
        else (
          record_state_comb v (v1, v2);
          fold_succ_e
            (fun (_, l1, u1) g ->
              fold_succ_e
                (fun (_, l2, u2) g ->
                  match L.(simp_opt ~is_bot @@ mk_and l1 l2) with
                  | Some l ->
                      add_edge_e (aux u1 u2 g) @@ E.create v l @@ u1 @ u2
                  | None -> g)
                g2 v2 g)
            g1 v1
          @@ add_vertex g v)
      in
      aux v1 v2 empty
  end

  (* module Dot = Graph.Graphviz.Dot (G) *)
  module PathCheck = Graph.Path.Check (G)

  module EdgeMapper =
    Graph.Gmap.Edge
      (G)
      (struct
        include G
        include Graph.Builder.P (G)
      end)

  type t = { init : G.V.t; finals : G.V.t list; graph : G.t }

  (* let pp_print ppf { init; finals; graph } = *)
  (*   let open Format in *)
  (*   let pp_regex ppf r = pp_print_string ppf @@ layout_regex r in *)
  (*   let pp_regexes ppf rs = *)
  (*     pp_print_list *)
  (*       ~pp_sep:(fun ppf () -> pp_print_string ppf ",") *)
  (*       pp_regex ppf rs *)
  (*   in *)
  (*   fprintf ppf "@[<v 2>init:@ %a@ finals:@ %a@ graph:@ %a@]" pp_regexes init *)
  (*     (pp_print_list pp_regexes) finals Dot.fprint_graph graph *)

  let to_dot_file filename layout_q layout_l { init; finals; graph } =
    let module Dot = Graph.Graphviz.Dot (struct
      include G

      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let default_edge_attributes _ = []
      let vertex_name v = "S_" ^ string_of_int @@ V.hash v

      let vertex_attributes v =
        [
          `Label (layout_q v);
          `Color
            (if V.equal v init then 0x00eeff
             else if finals |> List.exists @@ V.equal v then 0x00ee00
             else 0x000000);
        ]

      let edge_attributes e = [ `Label (layout_l @@ E.label e) ]
      let get_subgraph _ = None
    end) in
    let oc = open_out filename in
    Dot.output_graph oc graph;
    close_out oc

  (** intersect two automaton structures *)
  let intersect ~is_bot a1 a2 =
    let graph = G.inter ~is_bot (a1.init, a1.graph) (a2.init, a2.graph) in
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
  let quotient ~is_bot (init_num, dist_to_finals, numerator) denominator =
    let init = init_num @ denominator.init in
    let qinv = G.VTbl.create @@ (2 * G.nb_vertex denominator.graph) in
    let graph =
      G.inter ~qinv ~is_bot
        (init_num, numerator.graph)
        (denominator.init, denominator.graph)
    in
    let pathchecker = PathCheck.create graph in
    let finals =
      G.fold_vertex
        (fun v acc ->
          let v_den = snd @@ G.VTbl.find qinv v in
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
