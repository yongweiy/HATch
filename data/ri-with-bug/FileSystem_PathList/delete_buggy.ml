let rec delete (path : Path.t) : bool =
  if not (exists path) then false
  else
    let rec deleteChildren : Path.t -> unit =
     fun (parent : Path.t) ->
      let (bytes : Bytes.t) = get path in
      let (children : PathList.t) = getChildren bytes in
      if not (is_path_nil children) then
        let (child : Path.t) = path_hd children in
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

let[@assertRty] delete ?l:(path = (true : [%v: Path.t])) =
  {
    res = (true : [%v: bool]);
    eff =
      (let (bytes : Bytes.t) = (true : [%v: Bytes.t]) in
       let (child : Path.t) = (path == parent v : [%v: Path.t]) in
       Constrain (Get (path, bytes), MemChild (bytes, child, true)));
  }
