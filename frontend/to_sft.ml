open Sugar
open Syntax.RtyRaw.Sft
open To_aevent

let pprint_label : Label.t -> string = function
  | Pred (p, fns) ->
      spf "%s/[%s]" (pprint_pred p)
        (String.concat ";" @@ List.map pprint_func fns)
  | Epsilon (phi, evs) ->
      spf "ϵ⟨%s⟩/[%s]" (To_qualifier.layout phi)
        (String.concat ";" @@ List.map pprint_ev evs)

let pprint_dom _ = _failatwith __FILE__ __LINE__ "TODO: To_sft.pprint_dom"
let pprint sft = display pprint_label sft
