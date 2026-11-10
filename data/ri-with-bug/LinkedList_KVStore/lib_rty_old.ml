let[@libRty] putNext ?l:(k = (true : [%v: Ptr.t])) ?l:(a = (true : [%v: Ptr.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutNext ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getNext ((a : Ptr.t) [@ghost]) ?l:(k = (true : [%v: Ptr.t])) =
  {
    pre = nextP k a;
    res = (v == a : [%v: Ptr.t]);
    newadding = lastL && GetNext ((k [@d]), v, v == a);
  }

let[@libRty] delNext ((a : Ptr.t) [@ghost]) ?l:(k = (true : [%v: Ptr.t])) =
  {
    pre = nextP k a;
    res = (v == a : [%v: Ptr.t]);
    newadding = lastL && DelNext ((k [@d]), v, v == a);
  }

let[@libRty] hasPrev ?l:(k = (true : [%v: Ptr.t])) =
  [|
    {
      pre = _F (PutNext (x_0, (k [@d]), v, true));
      res = (v : [%v: bool]);
      newadding = lastL && HasPrev ((k [@d]), v, v);
    };
    {
      pre = not (_F (PutNext (x_0, (k [@d]), v, true)));
      res = (not v : [%v: bool]);
      newadding = lastL && HasPrev ((k [@d]), v, not v);
    };
  |]

let[@libRty] putVal ?l:(k = (true : [%v: Ptr.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutVal ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getVal ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Ptr.t])) =
  {
    pre = valP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetVal ((k [@d]), v, v == a);
  }
