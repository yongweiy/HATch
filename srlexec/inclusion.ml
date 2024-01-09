(** under-approximated inclusion check *)

open Zzdatatype.Datatype
open Language
open Syntax
open Rty
open Sugar
open Literal
open Deriv
open Sample

let check ?(constr = P.mk_true) r1 r2 =
  let time_t, trs = clock (fun () -> sample_regex ~constr r1) in
  Pp.printf "sample takes %f seconds\n" time_t;
  Choice.map
    (fun tr ->
      print_trace tr;
      let time_t, res = clock (fun () -> symb_match ~constr tr r2) in
      (* Pp.printf "symb_match takes %f seconds\n\n" time_t; *)
      res)
    trs
  |> Choice.forall

let%test_module "SRLexec" =
  (module struct
    open Type_dec.NT;;

    Env.load_meta "/home/slark/Desktop/PL-playground/HATs/meta-config.json";;
    Rty.Ax.init_builtin_axs []

    let lx = (AVar "x") #: int_ty
    let ly = (AVar "y") #: int_ty
    let op_lt = (Op.BuiltinOp "<") #: T.(mk_arr int_ty (mk_arr int_ty bool_ty))
    let op_gt = (Op.BuiltinOp ">") #: T.(mk_arr int_ty (mk_arr int_ty bool_ty))
    let op_eq = (Op.BuiltinOp "==") #: T.(mk_arr int_ty (mk_arr int_ty bool_ty))

    let op_neq =
      (Op.BuiltinOp "!=") #: T.(mk_arr int_ty (mk_arr int_ty bool_ty))

    let two = (AC (I 2)) #: int_ty
    let three = (AC (I 3)) #: int_ty
    let five = (AC (I 5)) #: int_ty
    let x_lt_two = Lit (AAppOp (op_lt, [ lx; two ]))
    let x_eq_two = Lit (AAppOp (op_eq, [ lx; two ]))
    let x_gt_two = Lit (AAppOp (op_gt, [ lx; two ]))
    let x_lt_three = Lit (AAppOp (op_lt, [ lx; three ]))
    let x_eq_three = Lit (AAppOp (op_eq, [ lx; three ]))
    let x_gt_three = Lit (AAppOp (op_gt, [ lx; three ]))
    let x_lt_five = Lit (AAppOp (op_lt, [ lx; five ]))
    let x_eq_five = Lit (AAppOp (op_eq, [ lx; five ]))
    let x_gt_five = Lit (AAppOp (op_gt, [ lx; five ]))
    let y_lt_two = Lit (AAppOp (op_lt, [ ly; two ]))
    let y_lt_three = Lit (AAppOp (op_lt, [ ly; three ]))
    let x_gt_y = Lit (AAppOp (op_gt, [ lx; ly ]))

    let%test "fwd_match1" =
      fwd_match
        [ EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = P.mk_true } ]
      @@ SeqA
           ( EventA
               (EffEvent
                  { op = "op"; vs = []; v = "x" #: int_ty; phi = P.mk_true }),
             EpsilonA )

    let%test "fwd_match2" =
      fwd_match
        [ EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_two } ]
      @@ SeqA
           ( EventA
               (EffEvent
                  { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_three }),
             EpsilonA )

    let%test "symb_match1" =
      symb_match
        (List.map Literal.of_sevent
           [
             EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = x_eq_two };
             EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = x_eq_five };
             EffEvent
               {
                 op = "op";
                 vs = [];
                 v = "x" #: int_ty;
                 phi = Or [ x_lt_two; x_gt_five ];
               };
           ])
      @@ StarA
           (LorA
              ( EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_three }),
                EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_three })
              ))

    (* let%test "next_literal" = *)
    (*   let lits = Choice.run_all @@ next_literal (StarA *)
    (*        (LorA *)
    (*           ( EventA *)
    (*               (EffEvent *)
    (*                  { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_three }), *)
    (*             EventA *)
    (*               (EffEvent *)
    (*                  { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_three }) *)
    (*           ))) in *)
    (*   print_trace lits; *)
    (*   true *)

    let%test "inclusion" =
      check
        (StarA
           (LorA
              ( EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_three }),
                EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_three })
              )))
        (StarA
           (LorA
              ( EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_lt_three }),
                EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_three })
              )))

    let%test "inclusion_with_uni_var" =
      check ~constr:y_lt_three
        (StarA
           (LorA
              ( EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_eq_five }),
                EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_y })
              )))
        (StarA
           (LorA
              ( EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_eq_three }),
                EventA
                  (EffEvent
                     { op = "op"; vs = []; v = "x" #: int_ty; phi = x_gt_three })
              )))
  end)
