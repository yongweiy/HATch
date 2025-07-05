open Syntax
open Sugar
module Raw = RtyRaw.Sft
open Rty.Sft
module A = Coersion_aevent

let force Raw.{ init; g } =
  (* Create a mapping from raw vertices to coerced vertices *)
  let vertex_map = Hashtbl.create (Raw.T.G.nb_vertex g) in
  let get_coerced_vertex raw_v =
    match Hashtbl.find_opt vertex_map raw_v with
    | Some coerced_v -> coerced_v
    | None ->
        let state = Raw.T.G.V.label raw_v in
        let coerced_v = T.G.V.create state in
        Hashtbl.add vertex_map raw_v coerced_v;
        coerced_v
  in
  
  (* Convert the graph structure *)
  let coerced_graph = 
    Raw.T.G.fold_edges_e
      (fun edge acc ->
        let src = Raw.T.G.E.src edge in
        let dst = Raw.T.G.E.dst edge in
        let label = Raw.T.G.E.label edge in
        let coerced_src = get_coerced_vertex src in
        let coerced_dst = get_coerced_vertex dst in
        let coerced_label = match label with
          | Raw.T.Label.Pred (pred, funcs) -> 
              T.Label.Pred (A.force_pred pred, List.map A.force_func funcs)
          | Raw.T.Label.Epsilon (prop, evs) ->
              T.Label.Epsilon (Coersion_qualifier.force prop, List.map A.force_ev evs)
        in
        let coerced_edge = T.G.E.create coerced_src coerced_label coerced_dst in
        T.G.add_edge_e acc coerced_edge)
      g
      T.G.empty
  in
  
  let coerced_init = get_coerced_vertex init in
  { init = coerced_init; g = coerced_graph }

let besome { init; g } =
  (* Create a mapping from coerced vertices to raw vertices *)
  let vertex_map = Hashtbl.create (T.G.nb_vertex g) in
  let get_raw_vertex coerced_v =
    match Hashtbl.find_opt vertex_map coerced_v with
    | Some raw_v -> raw_v
    | None ->
        let state = T.G.V.label coerced_v in
        let raw_v = Raw.T.G.V.create state in
        Hashtbl.add vertex_map coerced_v raw_v;
        raw_v
  in
  
  (* Convert the graph structure *)
  let raw_graph = 
    T.G.fold_edges_e
      (fun edge acc ->
        let src = T.G.E.src edge in
        let dst = T.G.E.dst edge in
        let label = T.G.E.label edge in
        let raw_src = get_raw_vertex src in
        let raw_dst = get_raw_vertex dst in
        let raw_label = match label with
          | T.Label.Pred (pred, funcs) -> 
              Raw.T.Label.Pred (A.besome_pred pred, List.map A.besome_func funcs)
          | T.Label.Epsilon (prop, evs) ->
              Raw.T.Label.Epsilon (Coersion_qualifier.besome prop, List.map A.besome_ev evs)
        in
        let raw_edge = Raw.T.G.E.create raw_src raw_label raw_dst in
        Raw.T.G.add_edge_e acc raw_edge)
      g
      Raw.T.G.empty
  in
  
  let raw_init = get_raw_vertex init in
  Raw.{ init = raw_init; g = raw_graph }
