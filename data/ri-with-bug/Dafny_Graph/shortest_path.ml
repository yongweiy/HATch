let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();
  markVisited start;

  (* Initialize current queue with start node *)
  let (current_queue : Queue.t) = create () in
  add start current_queue;

  (* Initialize next queue for next depth level *)
  let (next_queue : Queue.t) = create () in

  let rec bfs_loop : int -> Queue.t -> Queue.t -> int =
   fun (current_depth : int) (current : Queue.t) (next : Queue.t) ->
    if isEmpty current then
      if isEmpty next then -1 (* Target not reachable *)
      else
        (* Move to next depth level *)
        let (result : int) = bfs_loop (current_depth + 1) next current in
        result
    else
      let (current_node : Node.t) = take current in
      if node_eq current_node target then current_depth
      else
        (* Explore neighbors *)
        let (neighbors : Iterator.t) = getNeighbors current_node in
        let rec explore_loop : unit -> unit =
         fun (_ : unit) ->
          if hasNext current_node neighbors then (
            let (neighbor : Node.t) = next current_node neighbors in
            if not (isVisited neighbor) then (
              markVisited neighbor;
              add neighbor next);
            explore_loop ();
            ())
        in
        explore_loop ();
            (* let (neighbor : Node.t) = next neighbors in *)
            (* if not (isVisited neighbor) then ( *)
            (*   markVisited neighbor; *)
            (*   add neighbor next); *)
        let (result : int) = bfs_loop current_depth current next in
        result
  in

  let (final_result : int) = bfs_loop 0 current_queue next_queue in
  final_result

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  { ret = (v == 1 : [%v: int]); eff = Constrain ((), ()) }
