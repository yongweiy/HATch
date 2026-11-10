let insert (x : Elem.t) (root : Elem.t) : Elem.t =
  let (balance : Elem.t -> unit) =
   fun (node : Elem.t) ->
    let (nodeIsBlack : bool) = isBlack node in
    let (nodeIsLeaf : bool) = isLeaf node in
    if nodeIsBlack && not nodeIsLeaf then
      let (left : Elem.t) = getLeft node in
      let (right : Elem.t) = getRight node in

      (* Check for red-red violations and fix them *)
      let (leftIsLeaf : bool) = isLeaf left in
      let (leftIsRed : bool) = isRed left in
      if (not leftIsLeaf) && leftIsRed then
        let (leftLeft : Elem.t) = getLeft left in
        let (leftRight : Elem.t) = getRight left in
        let (leftLeftIsLeaf : bool) = isLeaf leftLeft in
        let (leftLeftIsRed : bool) = isRed leftLeft in
        let (leftRightIsLeaf : bool) = isLeaf leftRight in
        let (leftRightIsRed : bool) = isRed leftRight in
        if
          ((not leftLeftIsLeaf) && leftLeftIsRed)
          || ((not leftRightIsLeaf) && leftRightIsRed)
        then (
          (* Rebalance: make current node red, children black *)
          let (unit1 : unit) = setRed node in
          let (unit2 : unit) = setBlack left in
          if not leftLeftIsLeaf then (
            let (unit3 : unit) = setBlack leftLeft in
            unit3;
            if not leftRightIsLeaf then
              let (unit4 : unit) = setBlack leftRight in
              unit4))
        else
          let (rightIsLeaf : bool) = isLeaf right in
          let (rightIsRed : bool) = isRed right in
          if (not rightIsLeaf) && rightIsRed then
            let (rightLeft : Elem.t) = getLeft right in
            let (rightRight : Elem.t) = getRight right in
            let (rightLeftIsLeaf : bool) = isLeaf rightLeft in
            let (rightLeftIsRed : bool) = isRed rightLeft in
            let (rightRightIsLeaf : bool) = isLeaf rightRight in
            let (rightRightIsRed : bool) = isRed rightRight in
            if
              ((not rightLeftIsLeaf) && rightLeftIsRed)
              || ((not rightRightIsLeaf) && rightRightIsRed)
            then
              (* Rebalance: make current node red, children black *)
              let (unit5 : unit) = setRed node in
              let (unit6 : unit) = setBlack right in
              if not rightLeftIsLeaf then (
                let (unit7 : unit) = setBlack rightLeft in
                unit7;
                if not rightRightIsLeaf then
                  let (unit8 : unit) = setBlack rightRight in
                  unit8)
  in

  let rec ins : Elem.t -> Elem.t =
   fun (node : Elem.t) ->
    let (nodeIsLeaf : bool) = isLeaf node in
    if nodeIsLeaf then (
      (* Create new red node *)
      setRed x;
      setLeft x node;
      (* point to leaf *)
      setRight x node;
      (* point to leaf *)
      x)
    else if elem_lt x node then (
      let (leftChild : Elem.t) = getLeft node in
      let (newLeft : Elem.t) = ins leftChild in
      setLeft node newLeft;
      balance node;
      node)
    else if not (elem_lt node x) then (
      let (rightChild : Elem.t) = getRight node in
      let (newRight : Elem.t) = ins rightChild in
      setRight node newRight;
      balance node;
      node)
    else node (* element already exists *)
  in

  let (newRoot : Elem.t) = ins root in
  (* Ensure root is black *)
  setBlack newRoot;
  newRoot

let[@assertRty] insert ?l:(x = (true : [%v: Elem.t]))
    ?l:(root = (not (v == x) : [%v: Elem.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      (let (l1 : Elem.t) = (true : [%v: Elem.t]) in
       let (r1 : Elem.t) = (true : [%v: Elem.t]) in
       let (r2 : Elem.t) = (true : [%v: Elem.t]) in
       let (r3 : Elem.t) = (true : [%v: Elem.t]) in
       Constrain (IsBlack (root, true), IsBlack (root, false)));
  }
