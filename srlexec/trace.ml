open Language.Rty
open Literal
open Sugar

type atom =
  | TamperSeal
  (* every trace is allowed to have one `UntoucableFNO` indicating
     everything to its right it untouchable by `Deriv` *)
  | Atom of literal
  (* let `f` return trace  *)
  | Repeat of { from : lit; to_ : lit; tr : trace }

and trace = atom list
(** stored in reverse order for ease of appending
   TODO: might need a customized data structure *)

let rec layout_atom = function
  | TamperSeal -> "ω"
  | Atom x -> layout_literal x
  | Repeat { from; to_; tr } ->
      spf "[%s | i=%s..%s] " (layout_trace tr) (layout_lit from)
        (layout_lit to_)

and layout_trace tr = String.concat "; " @@ List.map layout_atom @@ List.rev tr

let print_trace tr = Pp.printf "%s\n" @@ layout_trace tr

let rec subst_atom yz = function
  | TamperSeal -> TamperSeal
  | Atom l -> Atom (subst yz l)
  | Repeat { from; to_; tr } -> Repeat { from; to_; tr = subst_trace yz tr }

and subst_trace yz = List.map (subst_atom yz)

let subst_trace_id (y, z) = subst_trace (y, AVar z)

let get_literal (tr : trace) =
  match tr with
  | [ Atom l ] -> l
  | _ ->
      _failatwith __FILE__ __LINE__
      @@ spf "Trace.get_literal %s" @@ layout_trace tr

let empty = []
let length = List.length

let take from tr =
  let len = length tr in
  _assert __FILE__ __LINE__ "Trace.sub" (from <= len);
  let rec aux (res, tr) i =
    match tr with
    | _ when i < from -> List.rev res
    | [] -> _failatwith __FILE__ __LINE__ "die"
    | x :: tr -> aux (x :: res, tr) (i - 1)
  in
  aux ([], tr) (len - 1)

let snoc x (tr : trace) = x :: tr
(* OSeq.cons (OSeq.return x) s *)

let snoc_repeat n f tr =
  let rec aux i s = if i = n then s else aux (i + 1) @@ snoc (f i) s in
  aux 0 tr
(* OSeq.append s @@ OSeq.init n f *)

let repeat n f = snoc_repeat n f empty

(* the trace `tr2` to be appended better be relatively short *)
let append tr1 tr2 = List.fold_right snoc tr2 tr1
(* OSeq.append s1 s2 *)

let fold : (atom -> 'acc -> 'acc) -> trace -> 'acc -> 'acc = List.fold_right
(* List.fold_right *)
(*   (fun x acc_opt -> *)
(*     let* acc = acc_opt in *)
(*     let+ l = match x with Single l -> Some l | _ -> None in *)
(*     f acc l) *)
(*   tr (Some acc) *)

let fold_lefti f acc (tr : trace) =
  snd @@ List.fold_right (fun x (i, acc) -> (i + 1, f i acc x)) tr (0, acc)

(* OSeq.map layout_literal >> OSeq.concat_string ~sep:";" *)
