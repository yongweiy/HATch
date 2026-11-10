let lazy_insert (x0 : Elem.t) (thunk : unit -> unit) (z : unit) : unit =
  let rec insert_aux : Elem.t -> unit =
    fun (x : Elem.t) ->
    let (k : Key.t) = randomKey () in
      if exists k then (
        insert_aux x;
        ())
      else (
        put k x;
        ())
  in
  thunk ();
  if not (hasValue x0) then ()
  else (
    insert_aux x0;
    ())

let[@assertRty] lazy_insert ((m : Elem.t) [@ghost])
    ?l:(x = (true : [%v: Elem.t]))
    ?l:(thunk =
        fun ?l:(y = (true : [%v: unit])) ->
          { pre = rI m; res = (true : [%v: unit]); post = rI m })
    ?l:(z = (true : [%v: unit])) =
  { pre = rI m; res = (true : [%v: unit]); post = rI m }
