let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();
  markVisited start;
  add start;

  (* Unroll 1: Process start node (depth 0, level_count=1) *)
  if isEmpty () then -1
  else
    let (node0 : Node.t) = take () in
    if node_eq node0 target then 0
    else
      let (neighbors0 : NodeList.t) = getNeighbors node0 in
      let (neighbor0 : Node.t) = hd neighbors0 in
      markVisited neighbor0;
      add neighbor0;
      let (next_count0 : int) = 1 in

      (* Unroll 2: Transition to depth 1 (level_count=0) *)
      let (depth1 : int) = 1 in
      let (level_count1 : int) = next_count0 in

      (* Unroll 3: Process first neighbor (depth 1, level_count=1) *)
      if isEmpty () then -1
      else
        let (node1 : Node.t) = take () in
        if node_eq node1 target then depth1
        else
          let (neighbors1 : NodeList.t) = getNeighbors node1 in
          let (neighbor1 : Node.t) = hd neighbors1 in
          markVisited neighbor1;
          add neighbor1;
          let (next_count1 : int) = 1 in

          (* Unroll 4: Transition to depth 2 (level_count=0) *)
          let (depth2 : int) = 2 in

          (* Unroll 5: Process second level neighbor (depth 2) *)
          if isEmpty () then -1
          else
            let (node2 : Node.t) = take () in
            if node_eq node2 target then depth2
            else -1

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  { ret = (v == 2 : [%v: int]); eff = Constrain ((), ()) }
