let lazy_insert (x : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  let rec insert_aux: Elem.t -> Elem.t -> unit = fun (cur : Elem.t) (y : Elem.t) ->
  if elem_eq cur y then ()
  else if not (elem_lt y cur) then
    if hasLeft cur then (
      let (left : Elem.t) = getLeft cur in
      insert_aux left y;
      ())
    else (
      addLeft cur y;
      ())
  else if hasRight cur then (
    let (right : Elem.t) = getRight cur in
    insert_aux right y;
    ())
  else (
    addRight cur y;
    ())
in
  thunk ();
  if hasRoot () then (
    let (root : Elem.t) = getRoot () in
    insert_aux root x;
    ())
  else (
    putRoot x;
    ())

let[@assertRty] lazy_insert ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI; res = (true : [%v: unit]); post = rI })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI; res = (true : [%v: unit]); post = rI }
