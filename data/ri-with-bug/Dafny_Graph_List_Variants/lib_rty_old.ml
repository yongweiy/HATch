(* HATch-format counterpart of lib_rty.ml (append-only history, every call is
   logged; see data/ri-with-bug/HATCH_SPECS.md).

   FIFO queue (isEmpty/add/take): lib_rty.ml's take Rejects (dequeues) the
   oldest Add.  Here the queue is tracked by successor: with [co] the value
   returned by the last Take, the head is the value added right after [co]
   (or the first Add if nothing was taken yet).  This is exact when added
   values are distinct, which add's precondition enforces (an
   under-approximation; BFS adds each node at most once since it marks nodes
   visited before adding them). *)

let[@libRty] isEmpty ((co : Node.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  [|
    {
      pre =
        (_G (not (Take (x, y, true))) && _G (not (Add (a, w, true))))
        || _F (Take (x, (co [@d]), true) && _X (_G (not (Take (x, y, true)))))
           && _F (Add ((co [@d]), w, true) && _X (_G (not (Add (a, w, true)))));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty (x_0, v, v);
    };
    {
      pre =
        (_G (not (Take (x, y, true))) && _F (Add (a, w, true)))
        || _F (Take (x, (co [@d]), true) && _X (_G (not (Take (x, y, true)))))
           && _F (Add ((co [@d]), w, true) && _X (_F (Add (a, w, true))));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty (x_0, v, not v);
    };
  |]

let[@libRty] add ?l:(a = (true : [%v: Node.t])) =
  {
    pre = not (_F (Add ((a [@d]), w, true)));
    res = (true : [%v: unit]);
    newadding = lastL && Add ((a [@d]), v, true);
  }

let[@libRty] take ((co : Node.t) [@ghost]) ((c : Node.t) [@ghost])
    ?l:(u = (true : [%v: unit])) =
  {
    pre =
      (_G (not (Take (x, y, true)))
      && _U (not (Add (b, w, true))) (Add ((c [@d]), w, true)))
      || _F (Take (x, (co [@d]), true) && _X (_G (not (Take (x, y, true)))))
         && _F
              (Add ((co [@d]), w, true)
              && _X (_U (not (Add (b, w, true))) (Add ((c [@d]), w, true))));
    res = (v == c : [%v: Node.t]);
    newadding = lastL && Take (x_0, v, v == c);
  }

(* Graph operations.  lib_rty.ml's connect Rejects a duplicate edge; here a
   duplicate edge is not allowed (under-approximation). *)
let[@libRty] connect ?l:(s1 = (true : [%v: Node.t])) ?l:(s2 = (true : [%v: Node.t])) =
  {
    pre = not (_F (Connect ((s1 [@d]), (s2 [@d]), u, true)));
    res = (true : [%v: unit]);
    newadding = lastL && Connect ((s1 [@d]), (s2 [@d]), v, true);
  }

(* exactly two edges out of [s], to [n1] then [n2]; the result lists them *)
let[@libRty] getNeighbors ((n1 : Node.t) [@ghost]) ((n2 : Node.t) [@ghost])
    ?l:(s = (true : [%v: Node.t])) =
  {
    pre =
      _U
        (not (Connect ((s [@d]), a, u, true)))
        (Connect ((s [@d]), (n1 [@d]), u, true)
        && _X
             (_U
                (not (Connect ((s [@d]), a, u, true)))
                (Connect ((s [@d]), (n2 [@d]), u, true)
                && _X (_G (not (Connect ((s [@d]), a, u, true)))))));
    res =
      (is_nil (tl (tl v)) && hd v == n1 && hd (tl v) == n2 : [%v: NodeList.t]);
    newadding = lastL && GetNeighbors ((s [@d]), v, true);
  }

let[@libRty] initVisited ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (not (MarkVisited (k, w, true)));
    res = (true : [%v: unit]);
    newadding = lastL && InitVisited (x_0, v, true);
  }

let[@libRty] markVisited ?l:(k = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && MarkVisited ((k [@d]), v, true);
  }

let[@libRty] isVisited ?l:(k = (true : [%v: Node.t])) =
  [|
    {
      pre =
        _U
          (not (MarkVisited ((k [@d]), u, true)))
          (MarkVisited ((k [@d]), u, true)
          && _X (_G (not (MarkVisited ((k [@d]), u, true)))));
      res = (v : [%v: bool]);
      newadding = lastL && IsVisited ((k [@d]), v, v);
    };
    {
      pre = _G (not (MarkVisited ((k [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && IsVisited ((k [@d]), v, not v);
    };
  |]
