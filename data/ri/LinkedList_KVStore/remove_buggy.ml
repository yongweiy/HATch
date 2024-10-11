let remove (hd: Ptr.t) (v: Elem.t) : Ptr.t =
  if is_nullptr hd then hd
  else if elem_eq (getVal hd) v then (
    let (next : Ptr.t) = getNext hd in
    next)
  else
    let rec iter : Ptr.t -> unit =
      fun (curr : Ptr.t) ->
      let (next : Ptr.t) = getNext curr in
      if is_nullptr next then ()
      else if elem_eq (getVal next) v then
        (putNext curr (getNext next); ())
      else iter next
    in
    iter hd; hd

let[@assertRty] remove ((a1 : Ptr.t) [@ghost]) ((a2 : Ptr.t) [@ghost])
     ?l:(hd = (not (is_nullptr a2) : [%v: Ptr.t])) ?l:(vl = (true : [%v: Elem.t])) =
  { pre = nextP a1 a2; res = (true : [%v: Ptr.t]);
    post = (nextP a1 a2; rI a1 a2)
  }
