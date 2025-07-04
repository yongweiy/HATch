open Sugar

module F (L : Lit.T) = struct
  module LAlg = Aevent.F (L)
  module T = StateMachine.Transducer.F (LAlg)
  include LAlg
  include T

  let subst yz =
    T.map ~f_pred:(subst_pred yz) ~f_func:(subst_func yz)
      ~f_prop:(subst_prop yz) ~f_ev:(subst_ev yz)

  let fv sft =
    T.fold ~f_pred:(List.append << fv_pred) ~f_func:(List.append << fv_func)
      ~f_prop:(List.append << fv_prop) ~f_ev:(List.append << fv_ev) sft []

  let normalize_name = T.map ~f_pred:normalize_name_pred ~f_func:Fun.id ~f_prop:Fun.id ~f_ev:Fun.id
end
