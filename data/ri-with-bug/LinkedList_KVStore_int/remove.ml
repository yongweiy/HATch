let remove (hd: int) (v: Elem.t) : int =
  if hd == 0 then hd
  else if elem_eq (getVal hd) v then getNext hd
  else
    let rec iter : int -> unit =
      fun (curr : int) ->
      let (next : int) = getNext curr in
      if next == 0 then ()
      else if elem_eq (getVal next) v then (
        let (nnext : int) = getNext next in
        putNext next 0;
        putNext curr nnext)
      else iter next
    in
    iter hd; hd

let[@assertRty] remove ((a : int) [@ghost]) ((b : int) [@ghost])
     ?l:(hd = (b != 0 : [%v: int])) ?l:(vl = (true : [%v: Elem.t])) =
  { pre = nextP a b; res = (true : [%v: int]);
    post = (nextP a b; rI a b)
  }
