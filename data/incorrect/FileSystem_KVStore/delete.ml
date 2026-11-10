(** user query: [path ∈ getChildren bytes_a; get a = bytes_a]
    
    witness: [put "a" {path}; put]
*)
let rec delete (path : Path.t) : unit =
  if isRoot path then ()
  else
    let (bytes : Bytes.t) = get path in
    if isDir bytes then (
      let (children : Path.t list) = getChildren bytes in
      List.iter delete children;
      ());
    let (parent : Path.t) = getParent path in
    let (bytes_of_parent : Bytes.t) = get parent in
    del path;
    (* invalidate the current path *)
    (* unlink from its parent *)
    put parent (delChild bytes_of_parent path);
    ()

let delete (path : Path.t) : unit =
  if isRoot path then ()
  else
    let rec aux (path : Path.t) : unit =
      let (bytes : Bytes.t) = get path in
      if isDir bytes then (
        let (children : Path.t list) = getChildren bytes in
        List.iter aux delete children;
        ());
      del path
    in
    aux path;
    let (parent : Path.t) = getParent path in
    let (bytes_of_parent : Bytes.t) = get parent in
    (* invalidate the current path *)
    (* unlink from its parent *)
    put parent (delChild bytes_of_parent path);
    ()
