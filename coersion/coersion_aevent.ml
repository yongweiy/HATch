open Syntax
module Raw = RtyRaw
open Rty
module Q = Coersion_qualifier

let force_pred ({ events; op_pred } : Raw.Sft.pred) : Sft.pred =
  {
    events =
      List.map
        (fun Raw.{ op; vs; v; phi } ->
          {
            op;
            vs = List.map (Coersion_aux.force __FILE__ __LINE__) vs;
            v = (Coersion_aux.force __FILE__ __LINE__) v;
            phi = Q.force phi;
          })
        events;
    op_pred =
      (match op_pred with
      | Blacklist (phi, ops) -> Blacklist (Q.force phi, ops)
      | Whitelist ops -> Whitelist ops);
  }

let besome_pred ({ events; op_pred } : Sft.pred) : Raw.Sft.pred =
  let events =
    List.map
      (fun { op; vs; v; phi } ->
        Raw.
          {
            op;
            vs = List.map Coersion_aux.besome vs;
            v = Coersion_aux.besome v;
            phi = Q.besome phi;
          })
      events
  in
  let op_pred : Raw.Sft.op_pred =
    match op_pred with
    | Blacklist (phi, ops) -> Blacklist (Q.besome phi, ops)
    | Whitelist ops -> Whitelist ops
  in
  { events; op_pred }

let force_ev Raw.Sft.{ op; args; ret } =
  Sft.
    {
      op;
      args = List.map Coersion_lit.force_typed args;
      ret = Coersion_lit.force_typed ret;
    }

let force_func : Raw.Sft.func -> Sft.func = function
  | IdentityF -> IdentityF
  | EventF ev -> EventF (force_ev ev)

let besome_ev Sft.{ op; args; ret } =
  Raw.Sft.
    {
      op;
      args = List.map Coersion_lit.besome_typed args;
      ret = Coersion_lit.besome_typed ret;
    }

let besome_func : Sft.func -> Raw.Sft.func = function
  | IdentityF -> IdentityF
  | EventF ev -> EventF (besome_ev ev)
