open Language

type 'a t = Found of RTypectx.ctx * Rty.Sft.sft * 'a | Fail | Go of 'a

