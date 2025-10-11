(** Convert SFT (Symbolic Finite Transducer) to regex using state elimination algorithm *)

open Zzdatatype.Datatype
open Sugar
open Language.Rty

module State = struct
  type t = Final | Normal [@@deriving sexp, compare, equal, hash]
end

module RegexLabel = struct
  type t = regex [@@deriving sexp, compare]
  (** Regex labels for graph edges in state elimination *)

  let default = EmptyA
end

module RegexGraph = struct
  include Graph.Persistent.Digraph.AbstractLabeled (State) (RegexLabel)

  let comb v1 v2 =
    V.create
    @@ match (V.label v1, V.label v2) with Final, Final -> Final | _ -> Normal

  let map_labels f g =
    fold_edges_e
      (fun e g ->
        add_edge_e (remove_edge_e g e)
        @@ E.create (E.src e) (f @@ E.label e) (E.dst e))
      g g

  let fold_labels f = fold_edges_e (E.label >> f)

  let filter_map_labels f g =
    fold_edges_e
      (fun e g ->
        match f @@ E.label e with
        | None -> g
        | Some l ->
            add_edge_e (remove_edge_e g e) @@ E.create (E.src e) l (E.dst e))
      g g

  let filter_vertices f g =
    fold_vertex (fun v g -> if f v then g else remove_vertex g v) g g

  let get_finals g =
    fold_vertex
      (fun v -> match V.label v with Final -> List.cons v | _ -> Fun.id)
      g []

  let merge g1 g2 =
    let g1, g2 = if nb_edges g1 < nb_edges g2 then (g1, g2) else (g2, g1) in
    fold_edges_e (Fun.flip add_edge_e) g1 g2
end

type regex_automaton = { init : RegexGraph.V.t; g : RegexGraph.t }
(** Regex-labeled automaton for state elimination *)

module VertexMap = Map.Make (Sft.G.V)
module RegexVertexMap = Map.Make (RegexGraph.V)
module SftToRegexMap = Map.Make (Sft.G.V)

(** Convert SFT transducer label to regex *)
let transducer_label_to_regex = function
  | Sft.Label.Pred (pred, _) ->
      let aux ev = EventA (EffEvent ev) in
      let events = List.map aux pred.events in
      let others =
        match pred.op_pred with
        | Whitelist ops -> List.map (aux << Sft.mk_event_from_op) ops
        | Blacklist (phi, ops) ->
            let r =
              mk_setMinusA
                ( mk_anyA,
                  List.fold_left
                    (fun r op -> mk_orA (r, aux @@ Sft.mk_event_from_op op))
                    EmptyA ops )
            in
            if is_true phi then [ r ]
            else [ mk_andA (EventA (GuardEvent phi), r) ]
      in
      List.fold_left (fun r s -> mk_orA (r, s)) EmptyA @@ events @ others
  | Sft.Label.Epsilon (phi, _) ->
      (* Convert guarded epsilon to regex epsilon *)
      EpsilonA phi

let transducer_labels_to_regex labels =
  List.fold_right
    (fun label r -> mk_seqA (transducer_label_to_regex label, r))
    labels mk_epsilon_true

(** Convert SFT to regex automaton *)
let sft_to_regex_automaton (sft : Sft.sft) =
  (* Map SFT vertices to regex vertices *)
  let vertex_map = ref VertexMap.empty in
  let get_regex_vertex sft_vertex =
    match VertexMap.find_opt sft_vertex !vertex_map with
    | Some regex_vertex -> regex_vertex
    | None ->
        let sft_state = Sft.G.V.label sft_vertex in
        let regex_state =
          match sft_state with
          | Sft.Final -> State.Final
          | Sft.Normal -> State.Normal
        in
        let regex_vertex = RegexGraph.V.create regex_state in
        vertex_map := VertexMap.add sft_vertex regex_vertex !vertex_map;
        regex_vertex
  in

  (* Convert transducer graph to regex-labeled graph *)
  let edges = Sft.G.fold_edges_e (fun edge acc -> edge :: acc) sft.g [] in
  let regex_g =
    List.fold_left
      (fun regex_g edge ->
        let src = Sft.G.E.src edge in
        let dst = Sft.G.E.dst edge in
        let label = Sft.G.E.label edge in
        let regex_label = transducer_label_to_regex label in
        let regex_src = get_regex_vertex src in
        let regex_dst = get_regex_vertex dst in
        let regex_edge = RegexGraph.E.create regex_src regex_label regex_dst in
        RegexGraph.add_edge_e regex_g regex_edge)
      RegexGraph.empty edges
  in
  let regex_init = get_regex_vertex sft.init in
  { init = regex_init; g = regex_g }

(** Convert regex automaton to GNFA following reference PDF algorithm *)
let to_gnfa regex_automaton =
  let { init; g } = regex_automaton in
  let finals = RegexGraph.get_finals g in

  (* Create new initial and final states *)
  let new_init = RegexGraph.V.create State.Normal in
  let new_final = RegexGraph.V.create State.Final in

  (* Start with empty graph and add new states *)
  let g' = RegexGraph.empty in
  let g' = RegexGraph.add_vertex g' new_init in
  let g' = RegexGraph.add_vertex g' new_final in

  (* Create vertex mapping from original to new graph *)
  let vertex_map = ref RegexVertexMap.empty in
  let g' =
    RegexGraph.fold_vertex
      (fun old_v g' ->
        let new_v = RegexGraph.V.create State.Normal in
        vertex_map := RegexVertexMap.add old_v new_v !vertex_map;
        RegexGraph.add_vertex g' new_v)
      g g'
  in
  let find_new_vertex old_v = RegexVertexMap.find old_v !vertex_map in

  (* Add epsilon transition from new_init to old initial *)
  let mapped_init_vertex = find_new_vertex init in
  let g' =
    RegexGraph.add_edge_e g'
      (RegexGraph.E.create new_init mk_epsilon_true mapped_init_vertex)
  in

  (* Add epsilon transitions from old finals to new_final *)
  let g' =
    List.fold_left
      (fun g' old_final ->
        let mapped_final_vertex = find_new_vertex old_final in
        RegexGraph.add_edge_e g'
          (RegexGraph.E.create mapped_final_vertex mk_epsilon_true new_final))
      g' finals
  in

  (* Copy all original edges *)
  let g' =
    RegexGraph.fold_edges_e
      (fun edge g' ->
        let src = RegexGraph.E.src edge in
        let dst = RegexGraph.E.dst edge in
        let label = RegexGraph.E.label edge in
        let new_src = find_new_vertex src in
        let new_dst = find_new_vertex dst in
        RegexGraph.add_edge_e g' (RegexGraph.E.create new_src label new_dst))
      g g'
  in

  (* Get all vertices in new graph *)
  let all_vertices = RegexGraph.fold_vertex (fun v acc -> v :: acc) g' [] in

  (* Add missing transitions with EmptyA (∅) labels *)
  let g' =
    List.fold_left
      (fun g src ->
        List.fold_left
          (fun g dst ->
            if RegexGraph.V.equal src dst then g
              (* Don't add self-loops with EmptyA *)
            else if RegexGraph.mem_edge g src dst then g
              (* Edge already exists *)
            else RegexGraph.add_edge_e g (RegexGraph.E.create src EmptyA dst))
          g all_vertices)
      g' all_vertices
  in

  { init = new_init; g = g' }

(** State elimination algorithm following reference PDF *)
let regex_automaton_to_regex regex_automaton =
  (* Convert to GNFA first *)
  let gnfa = to_gnfa regex_automaton in
  let { init; g } = gnfa in

  (* Find the single final state *)
  let finals = RegexGraph.get_finals g in
  let final =
    match finals with
    | [ f ] -> f
    | [] -> failwith "No final state in GNFA"
    | _ -> failwith "Multiple final states in GNFA"
  in

  (* Handle trivial cases *)
  if RegexGraph.nb_vertex g <= 2 then
    (* Should have only init and final, extract the direct transition *)
    if RegexGraph.mem_edge g init final then
      let edges = RegexGraph.find_all_edges g init final in
      let combined =
        List.fold_left
          (fun acc edge ->
            let label = RegexGraph.E.label edge in
            if equal_sfa acc EmptyA then label else LorA (acc, label))
          EmptyA edges
      in
      simpl combined
    else EmptyA
  else
    (* Main state elimination algorithm *)
    let vertices = RegexGraph.fold_vertex (fun v acc -> v :: acc) g [] in
    let intermediate_vertices =
      List.filter
        (fun v ->
          (not (RegexGraph.V.equal v init)) && not (RegexGraph.V.equal v final))
        vertices
    in

    (* Create transition table: vertex -> vertex -> regex *)
    let transition_table = ref RegexVertexMap.empty in
    let get_transition src dst =
      match RegexVertexMap.find_opt src !transition_table with
      | None -> EmptyA
      | Some dst_map -> (
          match RegexVertexMap.find_opt dst dst_map with
          | None -> EmptyA
          | Some regex -> regex)
    in
    let set_transition src dst regex =
      let dst_map =
        match RegexVertexMap.find_opt src !transition_table with
        | None -> RegexVertexMap.empty
        | Some m -> m
      in
      let new_dst_map = RegexVertexMap.add dst regex dst_map in
      transition_table := RegexVertexMap.add src new_dst_map !transition_table
    in

    (* Initialize transition table from graph edges *)
    RegexGraph.iter_edges_e
      (fun edge ->
        let src = RegexGraph.E.src edge in
        let dst = RegexGraph.E.dst edge in
        let label = RegexGraph.E.label edge in
        let existing = get_transition src dst in
        let combined =
          if equal_sfa existing EmptyA then label else LorA (existing, label)
          (* Union of parallel edges *)
        in
        set_transition src dst combined)
      g;

    (* Eliminate intermediate vertices one by one *)
    let rec eliminate_vertices remaining_vertices =
      match remaining_vertices with
      | [] -> ()
      | qrip :: rest ->
          (* Get self-loop of qrip *)
          let qrip_loop = get_transition qrip qrip in

          (* For each pair of vertices (qin, qout), update transition qin -> qout *)
          List.iter
            (fun qin ->
              List.iter
                (fun qout ->
                  if
                    (not (RegexGraph.V.equal qin qrip))
                    && not (RegexGraph.V.equal qout qrip)
                  then
                    let rin = get_transition qin qrip in
                    let rout = get_transition qrip qout in
                    let rdir = get_transition qin qout in

                    (* Formula from reference PDF: Rdir + Rin(Rrip)* Rout *)
                    let new_path =
                      if equal_sfa rin EmptyA || equal_sfa rout EmptyA then
                        EmptyA
                      else
                        let rrip_star =
                          if equal_sfa qrip_loop EmptyA then mk_epsilon_true
                          else StarA qrip_loop
                        in
                        SeqA (SeqA (rin, rrip_star), rout)
                    in
                    let updated =
                      if equal_sfa rdir EmptyA && equal_sfa new_path EmptyA then
                        EmptyA
                      else if equal_sfa rdir EmptyA then new_path
                      else if equal_sfa new_path EmptyA then rdir
                      else LorA (rdir, new_path)
                    in
                    set_transition qin qout (simpl updated))
                vertices)
            vertices;
          eliminate_vertices rest
    in

    eliminate_vertices intermediate_vertices;

    (* Extract final result: init -> final *)
    let result = get_transition init final in
    simpl result

(** Main function: convert SFT to regex *)
let sft_to_regex sft =
  let regex_automaton = sft_to_regex_automaton sft in
  regex_automaton_to_regex regex_automaton
