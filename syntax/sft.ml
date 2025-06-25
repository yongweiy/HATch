open Sugar

module F (L : Lit.T) = struct
  module LAlg = Aevent.F (L)
  module T = StateMachine.Transducer.F (LAlg)
  include LAlg
  include T

  let subst yz = T.map (subst_pred yz) (subst_func yz)

  let fv sft =
    T.fold (List.append << fv_pred) (List.append << fv_func) sft []

  let normalize_name = T.map normalize_name_pred Fun.id
end
