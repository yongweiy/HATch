let shortest_path (start : Node.t) (target : Node.t) : int =
  initVisited ();

  add start;
  let (node0 : Node.t) = take () in

  let (neighbors0 : NodeList.t) = getNeighbors node0 in
  let (neighbor1 : Node.t) = hd neighbors0 in
  add neighbor1;

  let (node1 : Node.t) = take () in
  if node_eq node1 target then 1
  else if node_eq node1 node0 then 3
  else (

    let (neighbors1 : NodeList.t) = getNeighbors node1 in
    let (neighbor2 : Node.t) = hd neighbors1 in

    (* add neighbor2; *)

    (* let (node2 : Node.t) = take () in *)
    if node_eq neighbor2 target then 2 else -1
  )

let[@assertRty] shortest_path ?l:(start = (true : [%v: Node.t]))
    ?l:(target = (true : [%v: Node.t])) =
  {
    ret = (v == 2 : [%v: int]);
    eff = Constrain (IsEmpty ((), true), IsEmpty ((), true));
  }
