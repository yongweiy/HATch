let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();
  markVisited start;

  let (current_queue : Queue.t) = create () in
  add start current_queue;
  let (next_queue : Queue.t) = create () in

  let rec bfs_loop : int -> Queue.t -> Queue.t -> int =
   fun (depth : int) (current : Queue.t) (next : Queue.t) ->
    if isEmpty current then
      if isEmpty next then -1
      else
        let (result : int) = bfs_loop (depth + 1) next current in
        result
    else
      let (current_node : Node.t) = take current in
      if node_eq current_node target then depth
      else
        let (neighbors : NodeList.t) = getNeighbors current_node in
        let rec explore_loop : NodeList.t -> unit =
         fun (ns : NodeList.t) ->
          if is_nil ns then ()
          else
            let (neighbor : Node.t) = hd ns in
            let (rest : NodeList.t) = tl ns in
            if not (isVisited neighbor) then (
              markVisited neighbor;
              add neighbor next;
              ());
            explore_loop rest;
            ()
        in
        explore_loop neighbors;
        let (result : int) = bfs_loop depth current next in
        result
  in

  let (final_result : int) = bfs_loop 0 current_queue next_queue in
  final_result

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  { ret = (v == 1 : [%v: int]); eff = Constrain ((), ()) }
