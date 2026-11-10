let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();
  markVisited start;

  add start;

  let rec bfs_loop : int -> int -> int -> int =
   fun (depth : int) (level_count : int) (next_count : int) ->
    if isEmpty () then -1
    else if level_count == 0 then
      (* Start new level *)
      let (res : int) = bfs_loop (depth + 1) next_count 0 in
      res
    else
      let (current_node : Node.t) = take () in
      if node_eq current_node target then depth
      else
        let (neighbors : NodeList.t) = getNeighbors current_node in
        let rec explore_loop : NodeList.t -> int -> int =
         fun (ns : NodeList.t) (count : int) ->
          if is_nil ns then count
          else
            let (neighbor : Node.t) = hd ns in
            let (rest : NodeList.t) = tl ns in
            if not (isVisited neighbor) then (
              markVisited neighbor;
              add neighbor;
              let (new_count : int) = explore_loop rest (count + 1) in
              new_count)
            else
              let (new_count : int) = explore_loop rest count in
              new_count
        in
        let (updated_next_count : int) =
          (* let (neighbor : Node.t) = hd neighbors in *)
          (* if not (isVisited neighbor) then ( *)
          (*   markVisited neighbor; *)
          (*   add neighbor; *)
          (*   let (new_count : int) = next_count + 1 in *)
          (*   new_count) *)
          (* else next_count *)
          explore_loop neighbors next_count
        in
        let (result : int) =
          bfs_loop depth (level_count - 1) updated_next_count
        in
        result
  in

  let (final_result : int) = bfs_loop 0 1 0 in
  final_result

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  {
    ret = (v == 2 : [%v: int]);
    eff = Constrain (IsEmpty ((), true), IsEmpty ((), true));
  }
