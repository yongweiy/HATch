open Sugar
open Core
open Language
open Rty
open Eff

(** CFG-based Bidirectional Search for Effect Verification
    
    This module builds a Control Flow Graph (CFG) from the effect language (Eff.t)
    and performs bidirectional search on it:
    
    - **Nodes**: Program points with accumulated context (bindings from entry)
    - **Edges**: Atomic operations (Bind, Guard, Trans, Call)
    - **Bidirectional search**: Explore from both entry and exit nodes simultaneously
*)

(** CFG node ID *)
type node_id = int [@@deriving sexp, compare, hash]

(** CFG edge: represents an atomic effect operation *)
type edge =
  | BindEdge of string Cty.ctyped    (* Existential binding *)
  | GuardEdge of Cty.prop             (* Guard condition *)
  | TransEdge of Trans.t              (* Transducer operation *)
  | CallEdge of Sft.ev                (* Effectful call *)
  | IdEdge                            (* Identity/no-op *)
[@@deriving sexp]

(** CFG node: represents a program point
    Note: Context is computed during search, not stored in nodes *)
type node = {
  id: node_id;
  mutable incoming: (node_id * edge) list;    (* (source_id, edge) *)
  mutable outgoing: (edge * node_id) list;    (* (edge, target_id) *)
}

(** Control Flow Graph *)
type cfg = {
  nodes: (node_id, node) Hashtbl.t;
  mutable entry: node_id;
  mutable exit: node_id;
  mutable next_id: int;
}

let create_cfg () = {
  nodes = Hashtbl.create (module Int);
  entry = 0;
  exit = 1;
  next_id = 2;
}

let fresh_node_id cfg =
  let id = cfg.next_id in
  cfg.next_id <- id + 1;
  id

let add_node cfg id =
  let node = { id; incoming = []; outgoing = [] } in
  Hashtbl.set cfg.nodes ~key:id ~data:node;
  node

let add_edge cfg from_id edge to_id =
  let from_node = Hashtbl.find_exn cfg.nodes from_id in
  let to_node = Hashtbl.find_exn cfg.nodes to_id in
  from_node.outgoing <- (edge, to_id) :: from_node.outgoing;
  to_node.incoming <- (from_id, edge) :: to_node.incoming

let get_node cfg id = Hashtbl.find_exn cfg.nodes id

(** Build CFG from effect expression
    Returns the exit node ID of the constructed subgraph *)
let rec build_cfg_from_eff cfg eff entry_id =
  match eff with
  | Atom Id ->
      (* Identity: entry connects directly to exit *)
      entry_id

  | Atom (Trans trans) ->
      (* Transducer: create new node and edge *)
      let exit_id = fresh_node_id cfg in
      let _ = add_node cfg exit_id in
      add_edge cfg entry_id (TransEdge trans) exit_id;
      exit_id

  | Atom (Call ev) ->
      (* Call: create new node and edge *)
      let exit_id = fresh_node_id cfg in
      let _ = add_node cfg exit_id in
      add_edge cfg entry_id (CallEdge ev) exit_id;
      exit_id

  | Bind ({ cx; cty }, eff') ->
      (* Bind: add binding edge then continue *)
      let mid_id = fresh_node_id cfg in
      let _ = add_node cfg mid_id in
      add_edge cfg entry_id (BindEdge { cx; cty }) mid_id;
      build_cfg_from_eff cfg eff' mid_id

  | Guard phi ->
      (* Guard: add guard edge *)
      let exit_id = fresh_node_id cfg in
      let _ = add_node cfg exit_id in
      add_edge cfg entry_id (GuardEdge phi) exit_id;
      exit_id

  | Seq (eff1, eff2) ->
      (* Sequential: build eff1, then eff2 from eff1's exit *)
      let mid_id = build_cfg_from_eff cfg eff1 entry_id in
      build_cfg_from_eff cfg eff2 mid_id

  | Choice (eff1, eff2) ->
      (* Choice: both branches start from entry, merge at new exit *)
      let end1 = build_cfg_from_eff cfg eff1 entry_id in
      let end2 = build_cfg_from_eff cfg eff2 entry_id in
      let exit_id = fresh_node_id cfg in
      let _ = add_node cfg exit_id in
      add_edge cfg end1 IdEdge exit_id;
      add_edge cfg end2 IdEdge exit_id;
      exit_id

  | Constrain (eff1, eff2) ->
      (* Constrain: process both effects sequentially *)
      let mid_id = build_cfg_from_eff cfg eff1 entry_id in
      build_cfg_from_eff cfg eff2 mid_id

(** Build complete CFG from effect *)
let build_cfg eff =
  let cfg = create_cfg () in
  let _ = add_node cfg cfg.entry in
  let exit_id = build_cfg_from_eff cfg eff cfg.entry in
  cfg.exit <- exit_id;
  cfg

(** Search state for bidirectional BFS *)
type search_state = {
  node_id: node_id;
  rctx: RTypectx.t;
  sfa: Sft.t;
  path: Eff.t;  (* Accumulated path *)
  steps: int;
}

(** Bidirectional BFS on CFG *)
let run opctx rctx eff post pre =
  Printf.printf "\n*** CFG_BIDIRECTIONAL.RUN CALLED ***\n";
  Out_channel.flush stdout;

  (* Build CFG from effect *)
  let cfg = build_cfg eff in
  Printf.printf "CFG built: %d nodes, entry=%d, exit=%d\n"
    (Hashtbl.length cfg.nodes) cfg.entry cfg.exit;
  Out_channel.flush stdout;

  (* Print CFG structure for debugging *)
  Hashtbl.iteri cfg.nodes ~f:(fun ~key:id ~data:node ->
    Printf.printf "Node %d: %d outgoing edges\n" id (List.length node.outgoing);
  );
  Out_channel.flush stdout;

  (* TODO: Implement actual CFG-based bidirectional search *)
  (* For now, delegate to the existing backward search *)
  Backwards.run opctx rctx eff post pre

