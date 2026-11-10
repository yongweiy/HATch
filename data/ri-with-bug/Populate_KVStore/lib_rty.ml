let[@libRty] put ?l:(k = (true : [%v: int])) ?l:(a = (true : [%v: int])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] get ((a : int) [@ghost]) ?l:(k = (true : [%v: int])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: int]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] exists ?l:(k = (true : [%v: int])) =
  [|
    {
      pre = existsP k;
      res = (v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, v);
    };
    {
      pre = not (existsP k);
      res = (not v : [%v: bool]);
      newadding = lastL && Exists ((k [@d]), v, not v);
    };
  |]

let[@libRty] hasValue ?l:(a = (true : [%v: int])) =
  [|
    {
      pre = has_valueP a;
      res = (v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, v);
    };
    {
      pre = not (has_valueP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, not v);
    };
  |]

let[@libRty] randomKey ?l:(k = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: int]);
    newadding = lastL && RandomKey (x_0, v, true);
  }
