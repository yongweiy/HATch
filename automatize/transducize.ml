open Zzdatatype.Datatype
open Sugar
open Language.Rty

(** Convert an automaton (Derivative.t) to a transducer (Sft.sft) where all output functions are identity *)
let admit_sft { Derivative.init; finals; graph } =
  (* Create a mapping from automaton vertices to transducer vertices *)
  let vertex_map = Hashtbl.create (Derivative.G.nb_vertex graph) in
  let get_trans_vertex auto_v =
    match Hashtbl.find_opt vertex_map auto_v with
    | Some trans_v -> trans_v
    | None ->
        let is_final = List.mem ~eq:Derivative.G.V.equal auto_v finals in
        let state = if is_final then Sft.Final else Sft.Normal in
        let trans_v = Sft.G.V.create state in
        Hashtbl.add vertex_map auto_v trans_v;
        trans_v
  in
  
  (* Convert the graph structure *)
  let trans_graph = 
    Derivative.G.fold_edges_e
      (fun edge acc ->
        let src = Derivative.G.E.src edge in
        let dst = Derivative.G.E.dst edge in
        let pred = Derivative.G.E.label edge in
        let trans_src = get_trans_vertex src in
        let trans_dst = get_trans_vertex dst in
        let trans_edge = Sft.T.G.E.create trans_src (Sft.T.Label.Pred (pred, [Sft.IdentityF])) trans_dst in
        Sft.T.G.add_edge_e acc trans_edge)
      graph
      Sft.T.G.empty
  in
  
  let trans_init = get_trans_vertex init in
  { Sft.T.init = trans_init; g = trans_graph }
