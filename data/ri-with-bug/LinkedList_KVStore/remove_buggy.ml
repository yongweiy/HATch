let remove (hd : Ptr.t) (vl : Elem.t) : Ptr.t =
  if is_nullptr hd then hd
  else if elem_eq (getVal hd) vl then
    let (next' : Ptr.t) = getNext hd in
    next'
  else
    let rec iter : Ptr.t -> unit =
     fun (curr : Ptr.t) ->
      let (next : Ptr.t) = getNext curr in
      if is_nullptr next then ()
      else (
        if elem_eq (getVal next) vl then (
          let (nnext : Ptr.t) = getNext next in
          let (null : Ptr.t) = get_nullptr () in
          putNext next null;
          putNext curr nnext;
          ())
        else ();
        iter next;
        ())
    in
    iter hd;
    hd

(* let remove (hd : Ptr.t) (vl : Elem.t) : Ptr.t = *)
(*   let (next : Ptr.t) = getNext hd in *)
(*   let (nnext : Ptr.t) = getNext next in *)
(*   let (null : Ptr.t) = get_nullptr () in *)
(*   putNext next null; *)
(*   putNext hd nnext; *)
(*   hd *)

(* let[@assertRty] remove ?l:(hd = (true : [%v: Ptr.t])) *)
(*     ?l:(vl = (true : [%v: Elem.t])) = *)
(*   { *)
(*     res = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (a : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        let (b : Ptr.t) = (not (v == a) : [%v: Ptr.t]) in *)
(*        let (c : Ptr.t) = (not (is_nullptr v) : [%v: Ptr.t]) in *)
(*        let (d : Ptr.t) = ((not (is_nullptr v)) && not (v == c) : [%v: Ptr.t]) in *)
(*        Constrain *)
(*          ( (GetNext (a, c); *)
(*             GetNext (b, d)), *)
(*            (GetNext (a, c); *)
(*             GetNext (b, c)) )); *)
(*   } *)

let[@assertRty] remove ?l:(hd = (not (is_nullptr v) : [%v: Ptr.t]))
    ?l:(vl = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      (let (a : Ptr.t) = (true : [%v: Ptr.t]) in
       let (b : Ptr.t) = (true : [%v: Ptr.t]) in
       let (c : Ptr.t) = (true : [%v: Ptr.t]) in
       Constrain
         ( (),
           (GetNext (ret, a);
            GetNext (a, b);
            GetNext (b, c);
            GetVal (c, vl)) ));
  }
