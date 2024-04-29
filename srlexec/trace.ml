open Literal
open Sugar

type trace = literal list
(** stored in reverse order for ease of appending
   TODO: might need a customized data structure *)

let empty = []
let snoc x tr = x :: tr
(* OSeq.cons (OSeq.return x) s *)

let snoc_repeat n f tr =
  let rec aux i s = if i = n then s else aux (i + 1) @@ snoc (f i) s in
  aux 0 tr
(* OSeq.append s @@ OSeq.init n f *)

let repeat n f = snoc_repeat n f empty

(* the trace `tr2` to be appended better be relatively short *)
let append tr1 tr2 = List.fold_right snoc tr2 tr1
(* OSeq.append s1 s2 *)

let fold_left f acc tr = List.fold_right (fun x acc -> f acc x) tr acc

let fold_lefti f acc tr =
  snd @@ List.fold_right (fun x (i, acc) -> (i + 1, f i acc x)) tr (0, acc)

let layout_trace = List.rev >> List.map layout_literal >> String.concat ";"
let print_trace tr = Pp.printf "%s\n" @@ layout_trace tr
let subst yz = List.map (subst yz)
let subst_id (y, z) = subst (y, AVar z)
(* OSeq.map layout_literal >> OSeq.concat_string ~sep:";" *)
