open Syntax
module Raw = RtyRaw
open Rty
module Cty = Coersion_cty
module SRL = Coersion_srl
module Aevent = Coersion_aevent
module SFT = Coersion_sft

let rec force_arr = function
  | Raw.(NormalArr { rx; rty }) -> NormalArr { rx; rty = force_rty rty }
  | Raw.GhostArr x -> GhostArr x
  | Raw.ArrArr rty -> ArrArr (force_rty rty)

and force_rty = function
  | Raw.BaseRty { cty } -> BaseRty { cty = Cty.force cty }
  | Raw.ArrRty { arr; rethty } ->
      ArrRty { arr = force_arr arr; rethty = force_hty rethty }

and force_hty = function
  | Raw.Rty rty -> Rty (force_rty rty)
  | Raw.Monad monad -> Monad (force_monad monad)
  | Raw.Htriple { pre; resrty; post } ->
      Htriple
        {
          pre = SRL.force pre;
          resrty = force_rty resrty;
          post = SRL.force post;
        }
  | Raw.Inter (hty1, hty2) -> Inter (force_hty hty1, force_hty hty2)

and force_trans : Raw.Trans.t -> Trans.t = function
  | Explicit sft -> Explicit (SFT.force sft)
  | Admit sfa -> Admit (SRL.force sfa)
  | Append ev -> Append (Aevent.force_ev ev)
  | Reject pred -> Reject (Aevent.force_pred pred)

and force_eff : Raw.Eff.t -> Eff.t = function
  | Atom atom -> Atom (force_eff_atom atom)
  | Constrain (eff1, eff2) -> Constrain (force_eff eff1, force_eff eff2)
  | Bind ({ cx; cty }, eff) -> Bind ({ cx; cty = Cty.force cty }, force_eff eff)
  | Guard prop -> Guard (Coersion_qualifier.force prop)
  | Seq (eff1, eff2) -> Seq (force_eff eff1, force_eff eff2)
  | Choice (eff1, eff2) -> Choice (force_eff eff1, force_eff eff2)

and force_eff_atom : Raw.Eff.atom -> Eff.atom = function
  | Id -> Id
  | Call ev -> Call (Aevent.force_ev ev)
  | Trans trans -> Trans (force_trans trans)

and force_monad : Raw.monad -> monad =
 fun { ret; eff } ->
  { ret = { rx = ret.rx; rty = force_rty ret.rty }; eff = force_eff eff }

let rec besome_arr = function
  | NormalArr { rx; rty } -> Raw.NormalArr { rx; rty = besome_rty rty }
  | GhostArr x -> Raw.GhostArr x
  | ArrArr rty -> Raw.ArrArr (besome_rty rty)

and besome_rty = function
  | BaseRty { cty } -> Raw.BaseRty { cty = Cty.besome cty }
  | ArrRty { arr; rethty } ->
      Raw.ArrRty { arr = besome_arr arr; rethty = besome_hty rethty }

and besome_hty = function
  | Rty rty -> Raw.Rty (besome_rty rty)
  | Monad monad -> Raw.Monad (besome_monad monad)
  | Htriple htriple -> besome_htriple htriple
  | Inter (hty1, hty2) -> Raw.Inter (besome_hty hty1, besome_hty hty2)

and besome_htriple { pre; resrty; post } =
  Raw.Htriple
    { pre = SRL.besome pre; resrty = besome_rty resrty; post = SRL.besome post }

and besome_monad : monad -> Raw.monad =
 fun { ret; eff } ->
  Raw.{ ret = { rx = ret.rx; rty = besome_rty ret.rty }; eff = besome_eff eff }

and besome_trans : Trans.t -> Raw.Trans.t = function
  | Explicit sft -> Explicit (SFT.besome sft)
  | Admit sfa -> Admit (SRL.besome sfa)
  | Append ev -> Append (Aevent.besome_ev ev)
  | Reject pred -> Reject (Aevent.besome_pred pred)

and besome_eff : Eff.t -> Raw.Eff.t = function
  | Atom atom -> Atom (besome_eff_atom atom)
  | Constrain (eff1, eff2) -> Constrain (besome_eff eff1, besome_eff eff2)
  | Bind ({ cx; cty }, eff) ->
      Bind ({ cx; cty = Cty.besome cty }, besome_eff eff)
  | Guard prop -> Guard (Coersion_qualifier.besome prop)
  | Seq (eff1, eff2) -> Seq (besome_eff eff1, besome_eff eff2)
  | Choice (eff1, eff2) -> Choice (besome_eff eff1, besome_eff eff2)

and besome_eff_atom : Eff.atom -> Raw.Eff.atom = function
  | Id -> Id
  | Call ev -> Call (Aevent.besome_ev ev)
  | Trans trans -> Trans (besome_trans trans)
