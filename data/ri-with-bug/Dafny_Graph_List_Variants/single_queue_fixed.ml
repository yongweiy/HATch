let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();
  markVisited start;

  let (queue : Queue.t) = create () in
  add start queue;

  (* Depth 0: Check if start is target *)
  if isEmpty queue then -1
  else
    let (node0 : Node.t) = take queue in
    if node_eq node0 target then 0
    else
      (* Explore neighbors of start (depth 1) *)
      let (neighbors0 : NodeList.t) = getNeighbors node0 in
      let rec explore_loop0 : NodeList.t -> unit =
       fun (ns : NodeList.t) ->
        if is_nil ns then ()
        else
          let (neighbor : Node.t) = hd ns in
          let (rest : NodeList.t) = tl ns in
          if not (isVisited neighbor) then
            markVisited neighbor;
            add neighbor queue;
            ()
          else ();
          explore_loop0 rest;
          ()
      in
      explore_loop0 neighbors0;

      (* Depth 1: Check nodes added from depth 0 *)
      if isEmpty queue then -1
      else
        let (node1 : Node.t) = take queue in
        if node_eq node1 target then 1
        else -1

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  { ret = (v == 1 : [%v: int]); eff = Constrain ((), ()) }
