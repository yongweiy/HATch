(* HATch-format counterpart of lib_rty.ml (append-only history, every call is
   logged; see data/ri-with-bug/HATCH_SPECS.md).  Existentials that lib_rty.ml
   binds inside an effect ([let (s : Set.t) = ... in]) are ghosts here, and a
   result that lib_rty.ml constrains through [ret] is a ghost [g] with
   [res = (v == g)].  lib_rty.ml's add Rejects a duplicate Add; duplicates stay
   in this append-only history (see HATCH_SPECS.md). *)

(* the new set has no elements yet *)
let[@libRty] create ((s : Set.t) [@ghost]) ?l:(u = (true : [%v: unit])) =
  {
    pre = _G (not (Add (a, (s [@d]), u, true)));
    res = (v == s : [%v: Set.t]);
    newadding = lastL && Create (x_0, v, v == s);
  }

let[@libRty] add ?l:(elem = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Add ((elem [@d]), (s [@d]), v, true);
  }

let[@libRty] mem ?l:(elem = (true : [%v: Elem.t])) ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre = _F (Add ((elem [@d]), (s [@d]), u, true));
      res = (v : [%v: bool]);
      newadding = lastL && Mem ((elem [@d]), (s [@d]), v, v);
    };
    {
      pre = not (_F (Add ((elem [@d]), (s [@d]), u, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && Mem ((elem [@d]), (s [@d]), v, not v);
    };
  |]

let[@libRty] isEmpty ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre = _G (not (Add (x_0, (s [@d]), u, true)));
      res = (v : [%v: bool]);
      newadding = lastL && IsEmpty ((s [@d]), v, v);
    };
    {
      pre = _F (Add (x_0, (s [@d]), u, true));
      res = (not v : [%v: bool]);
      newadding = lastL && IsEmpty ((s [@d]), v, not v);
    };
  |]

(* the new iterator is fresh; its set is recorded as set_of *)
let[@libRty] getIter ((it : Iter.t) [@ghost]) ?l:(s = (true : [%v: Set.t])) =
  {
    pre = _G (not (GetIter (r, (it [@d]), true)));
    res = (v == it && set_of v == s : [%v: Iter.t]);
    newadding = lastL && GetIter ((s [@d]), v, v == it);
  }

(* [it] was produced by getIter [s] *)
let[@libRty] hasIter ?l:(it = (true : [%v: Iter.t])) ?l:(s = (true : [%v: Set.t])) =
  [|
    {
      pre =
        _U
          (not (GetIter (r, (it [@d]), true)))
          (GetIter ((s [@d]), (it [@d]), true)
          && _X (_G (not (GetIter (r, (it [@d]), true)))));
      res = (v : [%v: bool]);
      newadding = lastL && HasIter ((it [@d]), (s [@d]), v, v);
    };
    {
      pre = _G (not (GetIter ((s [@d]), (it [@d]), true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasIter ((it [@d]), (s [@d]), v, not v);
    };
  |]

(* As lib_rty.ml: [e] is the first element added to set_of it (fresh
   iterator), or the element added right after [last], the element [it]
   returned last; the elements involved were added exactly once. *)
let[@libRty] next ((last : Elem.t) [@ghost]) ((e : Elem.t) [@ghost])
    ?l:(it = (true : [%v: Iter.t])) =
  {
    pre =
      (_U (not (Add ((e [@d]), y, u, y == set_of it))) (Add ((e [@d]), y, u, y == set_of it) && _X (_G (not (Add ((e [@d]), y, u, y == set_of it))))))
      && ((_U (not (Add (b, y, u, y == set_of it))) (Add ((e [@d]), y, u, y == set_of it) && _X (_F (GetIter (y, (it [@d]), y == set_of it) && _X (_G (not (Next ((it [@d]), b, true))))))))
         || ((_U (not (Add ((last [@d]), y, u, y == set_of it))) (Add ((last [@d]), y, u, y == set_of it) && _X (_G (not (Add ((last [@d]), y, u, y == set_of it)))))) && (_F (Add ((last [@d]), y, u, y == set_of it) && _X (_U (not (Add (b, y, u, y == set_of it))) (Add ((e [@d]), y, u, y == set_of it) && _X (_F (GetIter (y, (it [@d]), y == set_of it) && _X (_F (Next ((it [@d]), (last [@d]), true) && _X (_G (not (Next ((it [@d]), b, true))))))))))))));
    res = (v == e : [%v: Elem.t]);
    newadding = lastL && Next ((it [@d]), v, v == e);
  }

let[@libRty] hasNext ((last : Elem.t) [@ghost]) ?l:(it = (true : [%v: Iter.t])) =
  [|
    {
      pre = _F (Add ((last [@d]), y, u, y == set_of it) && _X (_F (GetIter (y, (it [@d]), y == set_of it) && _X (_G (not (Next ((it [@d]), (last [@d]), true)))))));
      res = (v : [%v: bool]);
      newadding = lastL && HasNext ((it [@d]), v, v);
    };
    {
      pre = (_U (not (Add (b, y, u, y == set_of it))) (GetIter (y, (it [@d]), y == set_of it))) || ((_U (not (Add ((last [@d]), y, u, y == set_of it))) (Add ((last [@d]), y, u, y == set_of it) && _X (_G (not (Add ((last [@d]), y, u, y == set_of it)))))) && (_F (Add ((last [@d]), y, u, y == set_of it) && _X (_U (not (Add (b, y, u, y == set_of it))) (GetIter (y, (it [@d]), y == set_of it) && _X (_F (Next ((it [@d]), (last [@d]), true) && _X (_G (not (Next ((it [@d]), b, true)))))))))));
      res = (not v : [%v: bool]);
      newadding = lastL && HasNext ((it [@d]), v, not v);
    };
  |]
