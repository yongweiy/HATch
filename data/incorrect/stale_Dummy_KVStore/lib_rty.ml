let[@libSRLRty] read ?l:(u = (true : [%v: unit])) =
  {
    ret = (true : [%v: Elem.t]);
    trans = (
      starT (not (Write (v, u, true)) / Id);
      Write ((ret [@d]), u, true) / Id;
      starT (not (Write (v, u, true)) / Id)
    );
  }

let[@libSRLRty] write ?l:(s = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    trans = (
      starT (
        (Write (v, u, true) / [| |]) |||
        not (Write (v, u, true)) / Id
      );
      (
        (Write (v, u, true) / Write (s, ()) ) |||
        (not (Write (v, u, true)) / [|Id; Write (s, ())|] )
      )
    );
  }

let[@libSRLRty] put ?l:(k = (true : [%v: Key.t])) ?l:(a = (true : [%v: Elem.t])) =
  {
    ret = (true : [%v: unit]);
    trans = (
      starT (
        (Put ((k [@d]), v, u, true) / [| |]) |||
        not (Put ((k [@d]), v, u, true)) / Id
      );
      (
        (Put ((k [@d]), v, u, true) / Put (k, a, ()) ) |||
        (not (Put ((k [@d]), v, u, true)) / [|Id; Put (k, a, ())|] )
      )
    );
  }

let[@libSRLRty] get ?l:(k = (true : [%v: Key.t])) =
  {
    ret = (true : [%v: Elem.t]);
    trans = (
      starT (not (Put ((k [@d]), v, u, true)) / Id);
      (Put ((k [@d]), (ret [@d]), u, true) / Id);
      starT (not (Put ((k [@d]), v, u, true)) / Id)
    );
  }

