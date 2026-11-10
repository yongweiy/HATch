let scrapeProfile (rootNode : Node.t) : unit =
  let extractNamePhone : Node.t -> Node.t -> unit =
   fun (nameNode : Node.t) (phoneNode : Node.t) ->
    let (nameId : int) = getNodeId nameNode in
    let (phoneId : int) = getNodeId phoneNode in
    putContact nameId phoneId;
    ()
  in

  let rec traverse : Node.t -> unit =
   fun (curr : Node.t) ->
    (* let rec traverseChildren : Iterator.t -> unit = *)
    (*  fun (iter : Iterator.t) -> *)
    (*   let (hasNext : bool) = hasNext iter in *)
    (*   if hasNext then ( *)
    (*     let (currentNode : Node.t) = next iter in *)
    (*     traverse currentNode; *)
    (*     traverseChildren iter; *)
    (*     ()) *)
    (* in *)
    let (children : Iterator.t) = getChildren curr in
    let (nodeClass : int) = getClassName curr in

    if nodeClass == 1 then (
      (* profile class = 1 *)
      (* Found a profile container, look for name and phone *)
      let (nameNode : Node.t) = findByClass children 2 in
      (* name class = 2 *)
      let (phoneNode : Node.t) = findByClass children 3 in

      extractNamePhone nameNode phoneNode;
      ());

    (* Continue traversing children *)
    let (currentNode : Node.t) = next curr children in
    let (hasNxt : bool) = hasNext curr children in
    (* traverseChildren children; *)
    ()
  in

  traverse rootNode;
  ()

let[@assertRty] scrapeProfile ?l:(rootNode = (true : [%v: Node.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (let (name : int) = (true : [%v: int]) in
       Constrain (MemContact (name, true), MemContact (name, false)));
  }
