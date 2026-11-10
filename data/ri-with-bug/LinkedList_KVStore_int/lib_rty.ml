let[@libRty] putNext ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: int]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutNext ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getNext ((a : int) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre = nextP k a;
    res = (v == a : [%v: int]);
    newadding = lastL && GetNext ((k [@d]), v, v == a);
  }

let[@libRty] putVal ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: Elem.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && PutVal ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] getVal ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre = valP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && GetVal ((k [@d]), v, v == a);
  }
