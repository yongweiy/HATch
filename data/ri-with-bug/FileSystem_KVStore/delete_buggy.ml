let rec delete (path : Path.t) : bool =
  if not (exists path) then false
  else
    let rec deleteChildren : Path.t -> unit =
     fun (parent : Path.t) ->
      let (bytes : Bytes.t) = get path in
      let (children : Iterator.t) = getChildren bytes in
      let (more : bool) = hasNext bytes children in
      if more then
        let (child : Path.t) = next bytes children in
        let (_b : bool) = delete child in
        ()
    in
    let (bytes : Bytes.t) = get path in
    let (down : bool) = isDir bytes in
    if down then deleteChildren path;
    del path;
    let (parent_path : Path.t) = getParent path in
    let (bytes_parent : Bytes.t) = get parent_path in
    delChild bytes_parent path;
    true

(* let[@libRty] deleteChildren ((p : Path.t) [@ghost]) *)
(*     ?l:(path = (true : [%v: Path.t])) = *)
(*   { pre = rI p; res = (true : [%v: unit]); post = rI p } *)

(* let[@assertRty] delete ?l:(path = (true : [%v: Path.t])) = *)
(*   { *)
(*     res = (true : [%v: bool]); *)
(*     eff = *)
(*       (let (p1 : Path.t) = (true : [%v: Path.t]) in *)
(*        let (p2 : Path.t) = (path == parent v : [%v: Path.t]) in *)
(*        Constrain (Exists (path, true), (Exists (p2, true)))); *)
(*   } *)

(* let[@assertRty] delete ?l:(path = (true : [%v: Path.t])) = *)
(*   { *)
(*     res = (true : [%v: bool]); *)
(*     eff = *)
(*       (let (p1 : Path.t) = (true : [%v: Path.t]) in *)
(*        let (p2 : Path.t) = (v == parent p1 : [%v: Path.t]) in *)
(*        Constrain *)
(*          ( Exists (p2, true), *)
(*            (Exists (p1, true); *)
(*             Exists (p2, false)) )); *)
(*   } *)

let[@assertRty] delete ?l:(path = (true : [%v: Path.t])) =
  {
    res = (true : [%v: bool]);
    eff =
      (let (bytes : Bytes.t) = (true : [%v: Bytes.t]) in
       let (child : Path.t) = (path == parent v : [%v: Path.t]) in
       Constrain (Get (path, bytes), MemChild (bytes, child, true)));
  }
