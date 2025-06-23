open Syntax
module Raw = RtyRaw
open Rty
module Q = Coersion_qualifier

let force_pred Raw.({ events; op_pred }) =
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
      | Raw.Blacklist (phi, ops) -> Blacklist (Q.force phi, ops)
      | Raw.Whitelist ops -> Whitelist ops);
  }

let besome_pred { events; op_pred } =
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
  let op_pred =
    match op_pred with
    | Blacklist (phi, ops) -> Raw.Blacklist (Q.besome phi, ops)
    | Whitelist ops -> Raw.Whitelist ops
  in
  Raw.{ events; op_pred }

let force_func = function
  | Raw.IdentityF -> IdentityF
  | Raw.EventF { op; args; ret } ->
      EventF
        {
          op;
          args = List.map Coersion_lit.force_typed args;
          ret = Coersion_lit.force_typed ret;
        }

let besome_func = function
  | IdentityF -> Raw.IdentityF
  | EventF { op; args; ret } ->
      Raw.EventF
        {
          op;
          args = List.map Coersion_lit.besome_typed args;
          ret = Coersion_lit.besome_typed ret;
        }
