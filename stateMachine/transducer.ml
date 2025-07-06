(** (mostly) finite state transducer *)

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin
open Zzdatatype.Datatype
open Sugar
open Sig

module State = struct
  type t = Final | Normal [@@deriving sexp, compare, equal, hash]
end

module F (A : ELA) = struct
  module Label = struct
    (** [Epsilon] label bears witness to [A.pred] but does not take
        input *)
    type t = Pred of A.pred * A.func list | Epsilon of A.P.prop * A.ev list
    [@@deriving sexp, compare]

    let default = Pred (A.mk_bot, [])
  end

  module G = struct
    include Graph.Persistent.Digraph.AbstractLabeled (State) (Label)

    let comb v1 v2 =
      V.create
      @@
      match (V.label v1, V.label v2) with Final, Final -> Final | _ -> Normal

    let map_labels f g =
      fold_edges_e
        (fun e g ->
          add_edge_e (remove_edge_e g e)
          @@ E.create (E.src e) (f @@ E.label e) (E.dst e))
        g g

    let fold_labels f = fold_edges_e (E.label >> f)

    let filter_map_labels f g =
      fold_edges_e
        (fun e g ->
          match f @@ E.label e with
          | None -> g
          | Some l ->
              add_edge_e (remove_edge_e g e) @@ E.create (E.src e) l (E.dst e))
        g g

    let filter_vertices f g =
      fold_vertex (fun v g -> if f v then g else remove_vertex g v) g g

    let get_finals g =
      fold_vertex
        (fun v -> match V.label v with Final -> List.cons v | _ -> Fun.id)
        g []
  end

  include State
  module PathCheck = Graph.Path.Check (G)

  type sft = { init : G.V.t; g : G.t }

  let sexp_of_sft _ = _failatwith __FILE__ __LINE__ "sexp_of_sft"
  let sft_of_sexp _ = _failatwith __FILE__ __LINE__ "sft_of_sexp"

  let display layout_l { init; g } =
    let module Dot = Graph.Graphviz.Dot (struct
      include G

      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let default_edge_attributes _ = []
      let vertex_name v = "S_" ^ string_of_int @@ V.hash v

      let vertex_attributes v =
        [
          `Label (vertex_name v);
          `Shape (match V.label v with Final -> `Doublecircle | _ -> `Circle);
          `Color (if V.equal init v then 0x00eeff else 0x000000);
        ]

      let edge_attributes e = [ `Label (layout_l @@ E.label e) ]
      let get_subgraph _ = None
    end) in
    let tmp_dot = Filename.temp_file "graph" ".dot" in
    let tmp_pdf = Filename.temp_file "graph" ".pdf" in
    let oc = open_out tmp_dot in
    Dot.output_graph oc g;
    close_out oc;
    ignore (Sys.command ("dot -Tpdf " ^ tmp_dot ^ " -o " ^ tmp_pdf));
    ignore (Sys.command ("evince " ^ tmp_pdf));
    Sys.remove tmp_dot;
    Sys.remove tmp_pdf

  let map ~f_pred ~f_func ~f_prop ~f_ev { init; g } =
    {
      init;
      g =
        G.map_labels
          (function
            | Pred (p, fns) -> Pred (f_pred p, List.map f_func fns)
            | Epsilon (phi, evs) -> Epsilon (f_prop phi, List.map f_ev evs))
          g;
    }

  let fold ~f_pred ~f_func ~f_prop ~f_ev { init; g } acc =
    G.fold_labels
      (function
        | Pred (p, fns) -> f_pred p >> List.fold_right f_func fns
        | Epsilon (phi, evs) -> f_prop phi >> List.fold_right f_ev evs)
      g acc

  let clean_moves ~is_bot { init; g } =
    {
      init;
      g =
        G.filter_map_labels
          (function
            | Pred (p, fns) ->
                Option.map (fun p -> Label.Pred (p, fns))
                @@ A.simp_opt ~is_bot p
            | Epsilon (phi, evs) when is_bot phi -> None
            | Epsilon (phi, evs) -> Some (Label.Epsilon (phi, evs)))
          g;
    }

  let clean_states { init; g } =
    assert (G.mem_vertex g init);
    let checker = PathCheck.create g in
    let is_reachable = PathCheck.check_path checker init in
    { init; g = G.filter_vertices is_reachable g }
  (* |> (tap @@ display (Sexplib.Std.string_of_sexp << Label.sexp_of_t)) *)

  let is_reachable { init; g } =
    let checker = PathCheck.create g in
    let aux = PathCheck.check_path checker init in
    List.exists aux @@ G.get_finals g

  let mk_atom p fns =
    let init = G.V.create Normal in
    let trans = G.E.create init (Pred (p, fns)) (G.V.create Final) in
    clean_states { init; g = G.add_edge_e G.empty trans }

  let mk_star_atom p fns =
    let init = G.V.create Final in
    let loop = G.E.create init (Pred (p, fns)) init in
    clean_states { init; g = G.add_edge_e G.empty loop }

  (** how to check graph equality *)
  let mk_ident = mk_star_atom A.mk_top [ A.mk_ident ]

  let mk_any = mk_star_atom A.mk_top []

  let mk_dom { init; g } =
    let g =
      G.map_labels
        (function
          | Pred (p, _) -> Pred (p, []) | Epsilon (phi, _) -> Epsilon (phi, []))
        g
    in
    { init; g }

  (** assume the image of functions labeled on a transition to be
      independent *)
  let mk_ran { init; g } =
    let g =
      G.fold_edges_e
        (fun e g ->
          let u, v = (G.E.src e, G.E.dst e) in
          let with_inputs ps =
            snd
            @@ List.fold_lefti
                 (fun (u, g) i p ->
                   let v =
                     if i + 1 = List.length ps then v else G.V.create Normal
                   in
                   (v, G.add_edge_e g @@ G.E.create u (Pred (p, [])) v))
                 (u, g) ps
          in
          match G.E.label e with
          | Pred (p, fns) -> with_inputs @@ List.map (A.mk_image p) fns
          | Epsilon (phi, evs) ->
              with_inputs
              @@ List.map (A.mk_and (A.from_prop phi) << A.ev_to_pred) evs)
        g G.empty
    in
    clean_states { init; g }

  let mk_concat { init = init1; g = g1 } { init = init2; g = g2 } =
    assert (not @@ G.mem_edge g2 init2 init2);
    let finals1 = G.get_finals g1 in
    let inits2 = List.map (fun _ -> G.V.create Normal) finals1 in
    let finals1_to_inits2 = List.combine finals1 inits2 in
    let convert_v1 v1 =
      match G.V.label v1 with
      | Final -> List.assoc ~eq:G.V.equal v1 finals1_to_inits2
      | Normal -> v1
    in
    let g2_copies =
      inits2
      |> List.map @@ fun init2' ->
         g2
         |> G.map_vertex @@ fun v ->
            if G.V.equal v init2 then init2' else G.V.create @@ G.V.label v
    in
    clean_states
      {
        init = convert_v1 init1;
        g =
          g1 |> G.map_vertex convert_v1
          |> List.fold_right (G.fold_edges_e (Fun.flip G.add_edge_e)) g2_copies;
      }

  (** TODO: how to enforce that incoming edges of [init1] and [init2]
      are labeled disjointly *)
  let mk_union { init = init1; g = g1 } { init = init2; g = g2 } =
    let g2 =
      G.map_vertex (fun v -> if G.V.equal init2 v then init1 else v) g2
    in
    clean_states
      { init = init1; g = G.fold_edges_e (Fun.flip G.add_edge_e) g2 g1 }

  module M = Map.Make (Graph.Util.CMPProduct (G.V) (G.V))

  (** a DFS procedure that, by assuming decidability of the label
      theory, eliminates incrementally all composed rules that have
      unsatisfiable guards and finally eliminates all deadends
      (deadlock states: states from which no final state is
      reachable) *)
  let mk_compose ~is_bot { init = init1; g = g1 } { init = init2; g = g2 } =
    let init = G.comb init1 init2 in
    let g = G.add_vertex G.empty init in
    let rec dfs ~m ~g v1 v2 v =
      match v1 with
      | `Go v1 when M.mem (v1, v2) m -> 
          (* Return existing combined vertex instead of just the graph *)
          let existing_v = M.find (v1, v2) m in
          g
      | `Go v1 ->
          let m = M.add (v1, v2) v m in
          G.fold_succ_e
            (fun e1 g ->
              match G.E.label e1 with
              | Pred (p1, fns1) ->
                  let v1' = G.E.dst e1 in
                  dfs ~m ~g (`Wait (p1, fns1, v1', A.mk_top, [])) v2 v
              | Epsilon (phi1, evs1) ->
                  let v1' = G.E.dst e1 in
                  dfs ~m ~g (`WaitEpsilon (evs1, v1', A.P.mk_true, [])) v2 v)
            g1 v1 g
      | `Wait (p1, [], v1, pred, fns) -> (
          let pred = A.mk_and pred p1 in
          match A.simp_opt ~is_bot pred with
          | Some pred ->
              let v' = 
                match M.find_opt (v1, v2) m with
                | Some existing_v -> existing_v
                | None -> G.comb v1 v2
              in
              let g = G.add_edge_e g @@ G.E.create v (Pred (pred, fns)) v' in
              dfs ~m ~g (`Go v1) v2 v'
          | None -> g)
      | `Wait (p1, fn1 :: fns1, v1, pred, fns) ->
          G.fold_succ_e
            (fun e2 g ->
              match G.E.label e2 with
              | Pred (p2, fns2) ->
                  let v2' = G.E.dst e2 in
                  let pred = A.(mk_and pred @@ mk_preimage p2 fn1) in
                  let fns =
                    fns @ List.map (fun fn2 -> A.compose fn2 fn1) fns2
                  in
                  dfs ~m ~g (`Wait (p1, fns1, v1, pred, fns)) v2' v
              | Epsilon (phi2, evs2) ->
                  let v2' = G.E.dst e2 in
                  let pred = A.(mk_and pred @@ from_prop phi2) in
                  let fns = fns @ List.map A.mk_const evs2 in
                  dfs ~m ~g (`Wait (p1, fn1 :: fns1, v1, pred, fns)) v2' v)
            g2 v2 g
      | `WaitEpsilon ([], v1, phi, evs) ->
          let v' = 
            match M.find_opt (v1, v2) m with
            | Some existing_v -> existing_v
            | None -> G.comb v1 v2
          in
          let g = G.add_edge_e g @@ G.E.create v (Epsilon (phi, evs)) v' in
          dfs ~m ~g (`Go v1) v2 v'
      | `WaitEpsilon (ev1 :: evs1, v1, phi, evs) ->
          G.fold_succ_e
            (fun e2 g ->
              match G.E.label e2 with
              | Pred (p2, fns2) ->
                  let v2' = G.E.dst e2 in
                  let phi =
                    A.(
                      P.mk_and phi @@ to_prop @@ mk_preimage p2 @@ mk_const ev1)
                  in
                  let compose_with_ev1 fn2 =
                    A.(force_const @@ compose fn2 @@ mk_const ev1)
                  in
                  let evs = evs @ List.map compose_with_ev1 fns2 in
                  dfs ~m ~g (`WaitEpsilon (evs1, v1, phi, evs)) v2' v
              | Epsilon (phi2, evs2) ->
                  let v2' = G.E.dst e2 in
                  let phi = A.P.mk_and phi phi2 in
                  let evs = evs @ evs2 in
                  dfs ~m ~g (`WaitEpsilon (ev1 :: evs1, v1, phi, evs)) v2' v)
            g2 v2 g
    in
    let g = dfs ~m:M.empty ~g (`Go init1) init2 init in
    clean_states { init; g }

  (** like interseciton of two SFAs *)
  let restrict_domain ~simp_pred { init = init1; g = sft }
      { init = init2; g = sfa } =
    assert (G.mem_vertex sft init1);
    assert (G.mem_vertex sfa init2);
    let init = G.comb init1 init2 in
    let g = G.add_vertex G.empty init in
    let rec dfs ~m ~g v1 v2 v =
      if M.mem (v1, v2) m then g
      else
        let m = M.add (v1, v2) v m in
        G.fold_succ_e
          (fun e1 g ->
            let v1' = G.E.dst e1 in
            match G.E.label e1 with
            | Pred (p1, fns1) ->
                G.fold_succ_e
                  (fun e2 g ->
                    let v2' = G.E.dst e2 in
                    match[@warning "-8"] G.E.label e2 with
                    | Epsilon (phi, evs) ->
                        let v' = G.comb v1 v2' in
                        let g =
                          G.add_edge_e g @@ G.E.create v (Epsilon (phi, evs)) v'
                        in
                        dfs ~m ~g v1 v2' v'
                    | Pred (p2, []) -> (
                        let v' = G.comb v1' v2' in
                        let p = A.mk_and p1 p2 in
                        match simp_pred p with
                        | None -> g
                        | Some p ->
                            dfs ~m
                              ~g:
                                (G.add_edge_e g
                                @@ G.E.create v (Pred (p, fns1)) v')
                              v1' v2' v'))
                  sfa v2 g
            | Epsilon (phi, evs) ->
                let v' = G.comb v1' v2 in
                let g =
                  G.add_edge_e g @@ G.E.create v (Epsilon (phi, evs)) v'
                in
                dfs ~m ~g v1' v2 v')
          sft v1 g
    in
    let g = dfs ~m:M.empty ~g init1 init2 init in
    clean_states { init; g }
end
