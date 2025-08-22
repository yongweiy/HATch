(** Convert SFT (Symbolic Finite Transducer) to regex using state elimination algorithm *)

open Zzdatatype.Datatype
open Sugar
open Language.Rty

(* Temporarily simplified for debugging module import issues *)
let sft_to_regex sft =
  (* TODO: implement proper SFT to regex conversion *)
  EmptyA

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
              mk_complementA
              @@ List.fold_left
                   (fun r op -> mk_orA (r, aux @@ Sft.mk_event_from_op op))
                   EmptyA ops
            in
            if is_true phi then [ r ]
            else [ mk_andA (EventA (GuardEvent phi), r) ]
      in
      List.fold_left (fun r s -> mk_orA (r, s)) EmptyA @@ events @ others
  | Sft.Label.Epsilon (phi, _) ->
      (* Convert guarded epsilon to regex epsilon *)
      EpsilonA phi

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

(** State elimination algorithm to convert regex automaton to single regex *)
let regex_automaton_to_regex regex_automaton =
  let { init; g } = regex_automaton in
  let finals = RegexGraph.get_finals g in

  (* Handle trivial cases *)
  if List.is_empty finals then EmptyA
  else if RegexGraph.nb_vertex g = 0 then EmptyA
  else if RegexGraph.nb_vertex g = 1 then
    (* Single vertex case *)
    if List.exists (RegexGraph.V.equal init) finals then mk_epsilon_true
    else EmptyA
  else
    (* Main state elimination algorithm *)
    let vertices = RegexGraph.fold_vertex (fun v acc -> v :: acc) g [] in
    let non_final_vertices =
      List.filter
        (fun v ->
          (not (List.exists (RegexGraph.V.equal v) finals))
          && not (RegexGraph.V.equal v init))
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
        in
        set_transition src dst combined)
      g;

    (* Add self-loops for vertices (epsilon transitions to self) *)
    List.iter
      (fun v ->
        let existing = get_transition v v in
        if equal_sfa existing EmptyA then set_transition v v mk_epsilon_true
        else set_transition v v (LorA (existing, mk_epsilon_true)))
      vertices;

    (* Eliminate intermediate vertices one by one *)
    let rec eliminate_vertices remaining_vertices =
      match remaining_vertices with
      | [] -> ()
      | q :: rest ->
          (* For each pair of vertices (p, r), update transition p -> r *)
          List.iter
            (fun p ->
              List.iter
                (fun r ->
                  if
                    (not (RegexGraph.V.equal p q))
                    && not (RegexGraph.V.equal r q)
                  then
                    let p_to_q = get_transition p q in
                    let q_to_q = get_transition q q in
                    let q_to_r = get_transition q r in
                    let p_to_r = get_transition p r in

                    (* New transition: p_to_r | (p_to_q . q_to_q* . q_to_r) *)
                    let q_star = StarA q_to_q in
                    let new_path = SeqA (SeqA (p_to_q, q_star), q_to_r) in
                    let updated = LorA (p_to_r, new_path) in
                    set_transition p r (simpl updated))
                vertices)
            vertices;
          eliminate_vertices rest
    in

    eliminate_vertices non_final_vertices;

    (* Collect final expressions: init -> final for each final state *)
    let final_expressions =
      List.filter_map
        (fun final ->
          let expr = get_transition init final in
          if equal_sfa expr EmptyA then None else Some expr)
        finals
    in

    (* Combine all paths to final states *)
    match final_expressions with
    | [] -> EmptyA
    | [ single ] -> simpl single
    | multiple ->
        simpl (List.fold_left (fun acc r -> LorA (acc, r)) EmptyA multiple)

(** Main function: convert SFT to regex *)
let sft_to_regex sft =
  let regex_automaton = sft_to_regex_automaton sft in
  regex_automaton_to_regex regex_automaton
