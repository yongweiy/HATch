let[@libRty] put ?l:(k = (true : [%v: Path.t])) ?l:(a = (true : [%v: Bytes.t]))
    =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && Put ((k [@d]), (a [@d]), v, true);
  }

let[@libRty] exists ?l:(k = (true : [%v: Path.t])) =
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

let[@libRty] get ((a : Bytes.t) [@ghost]) ?l:(k = (true : [%v: Path.t])) =
  {
    pre = storedP k a;
    res = (v == a : [%v: Bytes.t]);
    newadding = lastL && Get ((k [@d]), v, v == a);
  }

let[@libRty] del ?l:(k = (true : [%v: Path.t])) =
  {
    pre = existsP k;
    res = (true : [%v: unit]);
    newadding = lastL && Del ((k [@d]), v, true);
  }

let[@libRty] getParent ?l:(a = (true : [%v: Path.t])) =
  {
    pre = not (is_root a);
    res = (v == parent a : [%v: Path.t]);
    newadding = lastL && GetParent ((a [@d]), v, v == parent a);
  }

let[@libRty] isRoot ?l:(a = (true : [%v: Path.t])) =
  [|
    {
      pre = is_root a;
      res = (v : [%v: bool]);
      newadding = lastL && IsRoot ((a [@d]), v, v);
    };
    {
      pre = not (is_root a);
      res = (not v : [%v: bool]);
      newadding = lastL && IsRoot ((a [@d]), v, not v);
    };
  |]

let[@libRty] isDir ?l:(bytes = (true : [%v: Bytes.t])) =
  [|
    {
      pre = is_dir bytes;
      res = (v : [%v: bool]);
      newadding = lastL && IsDir ((bytes [@d]), v, v);
    };
    {
      pre = not (is_dir bytes);
      res = (not v : [%v: bool]);
      newadding = lastL && IsDir ((bytes [@d]), v, not v);
    };
  |]

let[@libRty] addChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    pre = is_dir bytes;
    res = (true : [%v: unit]);
    newadding = lastL && AddChild ((bytes [@d]), (child [@d]), v, true);
  }

let[@libRty] memChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  [|
    {
      pre = is_child bytes child;
      res = (v : [%v: bool]);
      newadding = lastL && MemChild ((bytes [@d]), (child [@d]), v, v);
    };
    {
      pre = not (is_child bytes child);
      res = (not v : [%v: bool]);
      newadding = lastL && MemChild ((bytes [@d]), (child [@d]), v, not v);
    };
  |]

let[@libRty] addChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && AddChild ((bytes [@d]), (child [@d]), v, true);
  }

let[@libRty] delChild ?l:(bytes = (true : [%v: Bytes.t]))
    ?l:(child = (true : [%v: Path.t])) =
  {
    pre = _G (Any true);
    res = (true : [%v: unit]);
    newadding = lastL && DelChild ((bytes [@d]), (child [@d]), v, true);
  }

let[@libRty] getChildren ?l:(bytes = (true : [%v: Bytes.t])) =
  {
    pre = is_dir bytes && not (has_child bytes);
    res = (is_path_nil v : [%v: PathList.t]);
    newadding = lastL && GetChildren ((bytes [@d]), v, true);
  }
