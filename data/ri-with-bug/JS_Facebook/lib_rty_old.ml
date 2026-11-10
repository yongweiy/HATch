(* HATch-format counterpart of lib_rty.ml (append-only history, every call is
   logged; see data/ri-with-bug/HATCH_SPECS.md).  lib_rty.ml's setters Reject
   the previous write, so reads here return the last write. *)

let[@libRty] setClassName ?l:(node = (true : [%v: Node.t])) ?l:(cls = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetClassName ((node [@d]), (cls [@d]), v, true);
  }

let[@libRty] getClassName ((cls : int) [@ghost]) ?l:(node = (true : [%v: Node.t])) =
  {
    pre =
      _F
        (SetClassName ((node [@d]), (cls [@d]), u, true)
        && _X (_G (not (SetClassName ((node [@d]), a, u, true)))));
    res = (v == cls : [%v: int]);
    newadding = lastL && GetClassName ((node [@d]), v, v == cls);
  }

let[@libRty] setNodeId ?l:(node = (true : [%v: Node.t])) ?l:(id = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && SetNodeId ((node [@d]), (id [@d]), v, true);
  }

let[@libRty] getNodeId ((id : int) [@ghost]) ?l:(node = (true : [%v: Node.t])) =
  {
    pre =
      _F
        (SetNodeId ((node [@d]), (id [@d]), u, true)
        && _X (_G (not (SetNodeId ((node [@d]), a, u, true)))));
    res = (v == id : [%v: int]);
    newadding = lastL && GetNodeId ((node [@d]), v, v == id);
  }

let[@libRty] addChild ?l:(parent = (true : [%v: Node.t])) ?l:(child = (true : [%v: Node.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddChild ((parent [@d]), (child [@d]), v, true);
  }

let[@libRty] getChildren ?l:(node = (true : [%v: Node.t])) =
  {
    pre = not (_F (GetChildren ((node [@d]), it, true)));
    res = (true : [%v: Iterator.t]);
    newadding = lastL && GetChildren ((node [@d]), v, true);
  }

(* a child [n] of [parent] (n <> parent) whose current class is [cls] *)
let[@libRty] findByClass ((n : Node.t) [@ghost]) ?l:(parent = (true : [%v: Node.t]))
    ?l:(cls = (true : [%v: int])) =
  {
    pre =
      _F
        (SetClassName ((n [@d]), (cls [@d]), u, true)
        && _X
             (_G (not (SetClassName ((n [@d]), a, u, true)))
             && _F (AddChild ((parent [@d]), (n [@d]), u, true))));
    res = (v == n && not (v == parent) : [%v: Node.t]);
    newadding = lastL && FindByClass ((parent [@d]), (cls [@d]), v, v == n);
  }

(* [iter] came from getChildren [parent]; lib_rty.ml binds [parent] and [child]
   existentially inside the effect, here they are ghosts *)
let[@libRty] hasNext ((parent : Node.t) [@ghost]) ((child : Node.t) [@ghost])
    ?l:(iter = (true : [%v: Iterator.t])) =
  [|
    {
      pre =
        _F
          (AddChild ((parent [@d]), (child [@d]), u, true)
          && _X
               (_F
                  (GetChildren ((parent [@d]), (iter [@d]), true)
                  && _X (not (_F (Next ((iter [@d]), (child [@d]), true)))))));
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((iter [@d]), v, v);
    };
    {
      pre =
        _U
          (not (AddChild ((parent [@d]), c, u, true)))
          (GetChildren ((parent [@d]), (iter [@d]), true));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((iter [@d]), v, not v);
    };
  |]

let[@libRty] next ((parent : Node.t) [@ghost]) ((c : Node.t) [@ghost])
    ?l:(iter = (true : [%v: Iterator.t])) =
  {
    pre =
      _F
        (AddChild ((parent [@d]), (c [@d]), u, true)
        && _X
             (_F
                (GetChildren ((parent [@d]), (iter [@d]), true)
                && _X (not (_F (Next ((iter [@d]), (c [@d]), true)))))));
    res = (v == c : [%v: Node.t]);
    newadding = lastL && Next ((iter [@d]), v, v == c);
  }

let[@libRty] putContact ?l:(id = (true : [%v: int])) ?l:(contact = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutContact ((id [@d]), (contact [@d]), v, true);
  }

let[@libRty] getContact ((contact : int) [@ghost]) ?l:(id = (true : [%v: int])) =
  {
    pre =
      _F
        (PutContact ((id [@d]), (contact [@d]), u, true)
        && _X (_G (not (PutContact ((id [@d]), a, u, true)))));
    res = (v == contact : [%v: int]);
    newadding = lastL && GetContact ((id [@d]), v, v == contact);
  }

let[@libRty] memContact ?l:(id = (true : [%v: int])) =
  [|
    {
      pre = _F (PutContact ((id [@d]), c, u, true));
      res = (v : [%v: bool]);
      newadding = lastL && MemContact ((id [@d]), v, v);
    };
    {
      pre = not (_F (PutContact ((id [@d]), c, u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && MemContact ((id [@d]), v, not v);
    };
  |]
