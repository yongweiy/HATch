let[@libRty] newCell ?l:(a = (true : [%v: unit])) =
  { ret = (true : [%v: Cell.t]); eff = Append (NewCell ((), ret)) }

let[@libRty] isCell ?l:(c = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (NewCell (u, v, v == c)))
                (NewCell (u, v, v == c)
                && _X (not (_F (NewCell (u, v, v == c))))))),
          (Guard (not ret);
           Admit (_G (not (NewCell (u, v, v == c))))) );
  }

let[@libRty] putCellContent ?l:(c = (true : [%v: Cell.t]))
    ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (PutCellContent ((c [@d]), b, u, true));
       Append (PutCellContent (c, a, ())));
  }

let[@libRty] hasCellContent ?l:(c = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (PutCellContent ((c [@d]), a, u, true)))
                (PutCellContent ((c [@d]), a, u, true)
                && _X (not (_F (PutCellContent ((c [@d]), a, u, true))))))),
          (Guard (not ret);
           Admit (_G (not (PutCellContent ((c [@d]), a, u, true))))) );
  }

let[@libRty] getCellContent ?l:(c = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Elem.t]);
    eff =
      Admit
        (_U
           (not (PutCellContent ((c [@d]), a, u, true)))
           (PutCellContent ((c [@d]), (ret [@d]), u, true)
           && _X (not (_F (PutCellContent ((c [@d]), a, u, true))))));
  }

let[@libRty] setNext ?l:(prev = (true : [%v: Cell.t]))
    ?l:(a = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: unit]);
    eff =
      (Reject (SetNext ((prev [@d]), a, u, true));
       Append (SetNext (prev, a, ())));
  }

let[@libRty] delNext ?l:(prev = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: unit]);
    eff = Reject (SetNext ((prev [@d]), a, u, true));
  }

let[@libRty] getNext ?l:(prev = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: Cell.t]);
    eff =
      Admit
        (_U
           (not (SetNext ((prev [@d]), a, u, true)))
           (SetNext ((prev [@d]), (ret [@d]), u, true)
           && _X (not (_F (SetNext ((prev [@d]), a, u, true))))));
  }

let[@libRty] hasNext ?l:(a = (true : [%v: Cell.t])) =
  {
    ret = (true : [%v: bool]);
    eff =
      Choice
        ( (Guard ret;
           Admit
             (_U
                (not (SetNext ((a [@d]), b, u, true)))
                (SetNext ((a [@d]), b, u, true)
                && _X (not (_F (SetNext ((a [@d]), c, v, true))))))),
          (Guard (not ret);
           Admit (_G (not (SetNext ((a [@d]), b, u, true))))) );
  }
