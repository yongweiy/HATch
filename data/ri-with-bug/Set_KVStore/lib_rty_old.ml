let[@libRty] put ?l:(k = (true : [%v: Key.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] get ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Key.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] exists ?l:(k = (true : [%v: Key.t])) =
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

(* true: some key [k] currently stores [a]; false: [a] was never stored
   (under-approximates: ignores values overwritten or deleted since) *)
let[@libRty] hasValue ((k : Key.t) [@ghost]) ?l:(a = (true : [%v: Elem.t])) =
  [|
    {
      pre = storedP k a;
      res = (v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, v);
    };
    {
      pre = not (has_valueP a);
      res = (not v : [%v: bool]);
      newadding = lastL && HasValue ((a [@d]), v, not v);
    };
  |]

let[@libRty] del ((a : Elem.t) [@ghost]) ?l:(k = (true : [%v: Key.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Elem.t]);
    newadding = lastL && Del ((k [@d]), v, v == a);
  }

let[@libRty] randomKey ?l:(k = (true : [%v: unit])) =
  {
    pre = _G (Any true);
    res = (true : [%v: Key.t]);
    newadding = lastL && RandomKey (x_0, v, true);
  }
