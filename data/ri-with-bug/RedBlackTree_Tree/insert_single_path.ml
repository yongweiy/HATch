let insert (x : Ptr.t) (root : Ptr.t) : Ptr.t =
  let (isRed : Ptr.t -> bool) =
   fun (node : Ptr.t) ->
    if is_nullptr node then false
    else
      let (ans : bool) = getColor node in
      ans
  in
  let (balance : Ptr.t -> Ptr.t) =
   fun (node : Ptr.t) ->
    let (nodeIsRed : bool) = getColor node in
    if nodeIsRed then node
    else
      let (left : Ptr.t) = getLeft node in
      let (leftIsRed : bool) = isRed left in
      let (right : Ptr.t) = getRight node in
      let (rightIsRed : bool) = isRed right in
      if leftIsRed then
        let (leftleft : Ptr.t) = getLeft left in
        let (leftleftIsRed : bool) = isRed leftleft in
        let (leftright : Ptr.t) = getRight left in
        let (leftrightIsRed : bool) = isRed leftright in
        if leftleftIsRed then (
          setRight left node;
          setLeft node leftright;
          setColor leftleft false;
          left)
        (* else if leftrightIsRed then ( *)
        (*   let (leftrightleft : Ptr.t) = getLeft leftright in *)
        (*   let (leftrightright : Ptr.t) = getRight leftright in *)
        (*   setColor left false; *)
        (*   setLeft leftright left; *)
        (*   setRight left leftrightleft; *)
        (*   setRight leftright node; *)
        (*   setLeft node leftrightright; *)
        (*   leftright) *)
        else node
      else if rightIsRed then node (* FIXME *)
      else node
  in
  (* let (right1 : Ptr.t) = getLeft root in *)
  (* let (right2 : Ptr.t) = getLeft right1 in *)
  (* let (right2 : Ptr.t) = balance right1 in *)
  (* setLeft right2 x; *)
  (* let (right2' : Ptr.t) = balance right2 in *)
  (* setRight right1 right2'; *)
  (* let (right1' : Ptr.t) = balance right1 in *)
  (* setRight root right1'; *)
  let (left : Ptr.t) = getLeft root in
  setRight left x;
  let (root' : Ptr.t) = balance root in
  root'
(* let (c : bool) = getColor root in *)
(* let (left : Ptr.t) = getLeft root in *)
(* let (cleft : bool) = getColor left in *)
(* let (right : Ptr.t) = getRight root in *)
(* let (cright : bool) = getColor right in *)
(* let (leftleft : Ptr.t) = getLeft left in *)
(* let (leftright : Ptr.t) = getRight left in *)
(* setColor leftleft false; *)
(* setRight left root; *)
(* setLeft root leftright; *)
(* left *)

let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t]))
    ?l:(root = (true : [%v: Ptr.t])) =
  {
    ret = (true : [%v: Ptr.t]);
    eff =
      (let (nil : Ptr.t) = (is_nullptr v : [%v: Ptr.t]) in
       let (l : Ptr.t) = ((not (is_nullptr v)) && not (v == x) : [%v: Ptr.t]) in
       let (r : Ptr.t) = ((not (is_nullptr v)) && not (v == x) : [%v: Ptr.t]) in
       Constrain
         ( (GetLeft (x, nil);
            GetRight (x, nil)),
           (GetLeft (x, l);
            GetRight (x, r)) ));
  }
(* let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t])) *)
(*     ?l:(root = (true : [%v: Ptr.t])) = *)
(*   { *)
(*     ret = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (what : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        Constrain (GetColor (what, true), GetColor (what, false))); *)
(*   } *)

(* let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t])) *)
(*     ?l:(root = (true : [%v: Ptr.t])) = *)
(*   { *)
(*     ret = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (p : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        let (q : Ptr.t) = (true : [%v: Ptr.t]) in *)
(*        Constrain *)
(*          ( (GetColor (p, false); GetColor (q, false)), *)
(*            (GetLeft (p, q); *)
(*             GetColor (p, true); *)
(*             GetColor (q, true)) )); *)
(*   } *)

(* let[@assertRty] insert ?l:(x = (true : [%v: Ptr.t])) *)
(*     ?l:(root = (true : [%v: Ptr.t])) = *)
(*   { *)
(*     ret = (true : [%v: Ptr.t]); *)
(*     eff = *)
(*       (let (l1 : Ptr.t) = (not (is_nullptr v) : [%v: Ptr.t]) in *)
(*        let (r1 : Ptr.t) = (not (is_nullptr v) && not (v == l1) : [%v: Ptr.t]) in *)
(*        let (r2 : Ptr.t) = (not (is_nullptr v) && not (v == r1) && not (v == l1) : [%v: Ptr.t]) in *)
(*        let (r3 : Ptr.t) = (not (is_nullptr v) && not (v == r1) && not (v == r2) && not (v == l1) : [%v: Ptr.t]) in *)
(*        let (leaf : Ptr.t) = (is_nullptr v : [%v: Ptr.t]) in *)
(*        Constrain *)
(*          ( (GetColor (root, false); *)
(*             GetColor (x, true); *)
(*             GetLeft (x, leaf); *)
(*             GetRight (x, leaf)), *)
(*            (GetLeft (root, l1); *)
(*             GetLeft (l1, leaf); *)
(*             GetRight (root, r1); *)
(*             GetRight (r1, r2); *)
(*             GetRight (r2, r3); *)
(*             GetRight (r3, leaf)) )); *)
(*   } *)
