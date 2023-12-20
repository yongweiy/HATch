open Zzdatatype.Datatype
open Language
open Syntax
open Sugar
open Rty

let rec is_nullable = function
  | EmptyA -> false
  | EpsilonA -> true
  | AnyA -> false
  | EventA (GuardEvent _) -> false
  | EventA (EffEvent _) -> false
  | LorA (r, s) -> is_nullable r || is_nullable s
  | LandA (r, s) -> is_nullable r && is_nullable s
  | SeqA (r, s) -> is_nullable r && is_nullable s
  | StarA _ -> true
  | ComplementA r -> not (is_nullable r)
  | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "is_nullable: SetMinusA"

let rec deriv r sev =
  match r with
  | EmptyA -> EmptyA
  | EpsilonA -> EmptyA
  | AnyA -> EpsilonA
  | EventA (GuardEvent _) ->
      _failatwith __FILE__ __LINE__ "deriv: GuardEvent UNIMP"
  | EventA (EffEvent { op; vs; v; phi }) when is_effevent_with_op op sev -> (
      let vs = List.map (fun typed -> typed.x) (v :: vs) in
      let fvs = fv_prop phi in
      let fvs = List.filter (fun v0 -> not (List.mem v0 vs)) fvs in
      _assert __FILE__ __LINE__ "deriv: free variable UNIMP"
      @@ List.is_empty fvs;
      let[@warning "-8"] (EffEvent effev) = sev in
      (* TODO: assert vs and v of the current event align *)
      match Smtquery.check (Implies (effev.phi, phi)) with
      | None -> EpsilonA
      | Some _ -> EmptyA)
  | EventA (EffEvent { op; vs; v; phi }) ->
      _assert __FILE__ __LINE__ "deriv: GuardEvent UNIMP" @@ is_effevent sev;
      EmptyA
  | LorA (r, s) -> LorA (deriv r sev, deriv s sev)
  | LandA (r, s) -> LandA (deriv r sev, deriv s sev)
  | SeqA (r, s) ->
      if is_nullable r then LorA (SeqA (deriv r sev, s), deriv s sev)
      else SeqA (deriv r sev, s)
  | StarA r -> SeqA (deriv r sev, StarA r)
  | ComplementA r -> ComplementA (deriv r sev)
  | SetMinusA (r, s) -> _failatwith __FILE__ __LINE__ "deriv: SetMinusA"

let fwd_match sev_list regex =
  List.fold_left deriv regex sev_list |> is_nullable

let bwd_match sev_list regex =
  List.rev sev_list |> List.fold_left deriv regex |> is_nullable

open Type_dec.NT

let%test "fwd_match1" =
  Env.load_meta "/home/slark/Desktop/PL-playground/HATs/meta-config.json";
  Rty.Ax.init_builtin_axs [];
  let regex =
    SeqA
      ( EventA
          (EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = mk_true }),
        EpsilonA )
  in
  let sev_list =
    [
      EffEvent
        { op = "op"; vs = []; v = "x" #: Type_dec.NT.int_ty; phi = mk_true };
    ]
  in
  fwd_match sev_list regex

let%test "fwd_match2" =
  Env.load_meta "/home/slark/Desktop/PL-playground/HATs/meta-config.json";
  Rty.Ax.init_builtin_axs [];
  let lx = (AVar "x") #: int_ty in
  let op_lt = (Op.BuiltinOp "<") #: T.(mk_arr int_ty (mk_arr int_ty bool_ty)) in
  let two = (AC (I 2)) #: int_ty in
  let three = (AC (I 3)) #: int_ty in
  let x_lt_two = AAppOp (op_lt, [ lx; two ]) in
  let x_lt_three = AAppOp (op_lt, [ lx; three ]) in
  let regex =
    StarA
      (EventA
         (EffEvent
            { op = "op"; vs = []; v = "x" #: int_ty; phi = Lit x_lt_three }))
  in
  let sev_list =
    [ EffEvent { op = "op"; vs = []; v = "x" #: int_ty; phi = Lit x_lt_two } ]
  in
  fwd_match sev_list regex
