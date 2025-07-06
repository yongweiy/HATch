open Zzdatatype.Datatype
(** graph whose vertices are derivatives *)

open Sugar
open Language.Rty
open Sft

include
  StateMachine.Automaton.F
    (struct
      type t = regex [@@deriving sexp, compare, equal, hash]

      let ( @ ) r1 r2 = LandA (r1, r2)
    end)
    (LAlg)

let from_regex ~is_bot =
  let quotient l r =
    let rec aux = function
      | EmptyA | EpsilonA -> EmptyA
      | AnyA -> EpsilonA
      | EventA sev when LAlg.entails_sevent ~check:(not << is_bot) l sev ->
          EpsilonA
      | EventA _ -> EmptyA
      | LorA (r, s) -> mk_orA (aux r, aux s)
      | LandA (r, s) -> mk_andA (aux r, aux s)
      | SeqA (r, s) when is_nullable r -> mk_orA (mk_seqA (aux r, s), aux s)
      | SeqA (r, s) -> mk_seqA (aux r, s)
      | StarA r -> mk_seqA (aux r, mk_starA r)
      | ComplementA r -> mk_complementA (aux r)
      | SetMinusA (r, s) -> aux @@ mk_andA (r, mk_complementA s)
    in
    aux r
  in
  let rec next = function
    | EmptyA | EpsilonA -> []
    | AnyA -> [ LAlg.mk_top ]
    | EventA sev -> [ LAlg.of_sevent sev ]
    | LorA (r, s) -> LAlg.join (next r) (next s)
    | LandA (r, s) -> List.cartesian_map LAlg.mk_and (next r) (next s)
    | SeqA (r, s) when is_nullable r -> LAlg.join (next r) (next s)
    | SeqA (r, s) -> next r
    | StarA r -> next r
    | ComplementA r ->
        let lits = next r in
        (LAlg.mk_not @@ LAlg.mk_or_list lits) :: lits
    | SetMinusA (AnyA, EventA sev) -> [ LAlg.mk_not @@ LAlg.of_sevent sev ]
    | SetMinusA (r, s) -> next @@ mk_andA (r, mk_complementA s)
  in
  let rec aux r g =
    if G.mem_vertex g r then g
    else
      next r
      |> List.map (simp_opt ~is_bot)
      |> List.keep_some
      |> List.filter_map (fun l ->
             let s = quotient l r in
             if is_empty s then None else Some (l, s))
      |> List.sort_and_combine
           (fun (_, r) (_, s) -> compare_regex r s)
           (fun (l_r, r) (l_s, s) -> (LAlg.mk_or l_r l_s, r))
      |> List.fold_left
           (fun g (l, s) -> G.add_edge_e (aux s g) @@ G.E.create r l s)
           (G.add_vertex g r)
  in
  fun r ->
    let graph = aux r G.empty in
    let finals =
      G.fold_vertex
        (fun v acc -> if is_nullable v then v :: acc else acc)
        graph []
    in
    { init = r; finals; graph }
