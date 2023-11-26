open Ppx_hash_lib.Std
open Hash.Builtin

module FuncExpr = struct
  type t = App of { name : string; args : t list } | Var of string
  [@@deriving eq, ord, hash, show]
end

module EqCons = struct
  type t = Eq of FuncExpr.t * FuncExpr.t [@@deriving eq, ord, show]
end

module L = struct
  module A = struct
    type t = EqCons.t [@@deriving eq, ord, show]

    let pp (f : Format.formatter) (e : t) = Format.fprintf f "%s" (show e)
  end

  type t = Neg of A.t | Pos of A.t [@@deriving eq, ord, show]
end

module ConstName = struct
  include CCString
end

module ProofLabel = struct
  type t = FuncExpr.t * FuncExpr.t

  let compare = CCPair.compare FuncExpr.compare FuncExpr.compare
  let default = (FuncExpr.Var "", FuncExpr.Var "")
end

module TermGraph = Graph.Persistent.Digraph.ConcreteBidirectional (FuncExpr)
module TermSet = CCSet.Make (FuncExpr)

let union_list lst = CCList.fold_left TermSet.union TermSet.empty lst

let rec subterms (term : FuncExpr.t) : TermSet.t =
  match term with
  | Var s -> TermSet.singleton (FuncExpr.Var s)
  | App { name = _; args } as c ->
      TermSet.add c (union_list (CCList.map subterms args))

let edges_of_term (term : FuncExpr.t) : TermGraph.E.t list =
  match term with
  | App { name = _; args } -> CCList.map (fun x -> (term, x)) args
  | Var _ -> []

let term_to_term_graph (term : FuncExpr.t list) : TermGraph.t =
  let term_set = CCList.map subterms term |> union_list |> TermSet.to_list in
  let base_graph =
    CCList.fold_left TermGraph.add_vertex TermGraph.empty term_set
  in
  CCList.fold_left TermGraph.add_edge_e base_graph
    (CCList.flat_map edges_of_term term_set)

let formula_to_term_graph (form : L.A.t list) : TermGraph.t =
  CCList.flat_map (fun x -> match x with EqCons.Eq (x, y) -> [ x; y ]) form
  |> term_to_term_graph

module UnionToLit = Map.Make (struct
  type t = FuncExpr.t * FuncExpr.t

  let compare = CCPair.compare FuncExpr.compare FuncExpr.compare
end)

module TermMap = Map.Make (FuncExpr)

module ProofForest = struct
  module G =
    Graph.Persistent.Digraph.ConcreteBidirectionalLabeled
      (FuncExpr)
      (ProofLabel)

  type t = { graph : G.t; ranks : int TermMap.t }

  let empty = { graph = G.empty; ranks = TermMap.empty }

  let rec collect_root_path (forest : G.t) (e : FuncExpr.t) : G.edge list =
    let succs = G.succ_e forest e in
    CCList.append succs
      (CCList.flat_map (fun (_, _, dst) -> collect_root_path forest dst) succs)

  (* this cannot be called if they are already in the same UF set *)
  let union (forest : t) (root : FuncExpr.t) (child : FuncExpr.t)
      (flipped : bool) : t =
    let rpath = collect_root_path forest.graph child in
    let flipped_path =
      CCList.map (fun (src, lbl, dst) -> (dst, lbl, src)) rpath
    in
    let removed_pth = CCList.fold_left G.remove_edge_e forest.graph rpath in
    let new_pth = CCList.fold_left G.add_edge_e removed_pth flipped_path in
    let label = if flipped then (child, root) else (root, child) in
    let fixed_graph = G.add_edge_e new_pth (child, label, root) in
    let orig_root_rank = TermMap.find root forest.ranks in
    let orig_child_rank = TermMap.find root forest.ranks in
    let new_child_rank = orig_child_rank + CCList.length rpath in
    let new_root = new_child_rank + orig_root_rank in
    let updates_for_child_dsts =
      CCList.mapi (fun i (_, _, nd) -> (nd, i + 1)) rpath
    in
    let new_mp =
      TermMap.add_seq
        ((root, new_root) :: (child, new_child_rank) :: updates_for_child_dsts
        |> CCList.to_seq)
        forest.ranks
    in
    { graph = fixed_graph; ranks = new_mp }

  let add_node_if_not_present (forest : t) (e1 : FuncExpr.t) : t =
    if TermMap.mem e1 forest.ranks then forest
    else
      {
        graph = G.add_vertex forest.graph e1;
        ranks = TermMap.add e1 1 forest.ranks;
      }

  let apply_union (forest : t) (e1 : FuncExpr.t) (e2 : FuncExpr.t) : t =
    let nf = add_node_if_not_present (add_node_if_not_present forest e1) e2 in
    let e1rank = TermMap.find e1 nf.ranks in
    let e2rank = TermMap.find e2 nf.ranks in
    let root, child = if e1rank <= e2rank then (e1, e2) else (e2, e1) in
    union nf root child (e1rank > e2rank)

  let lca (forest : t) (e1 : FuncExpr.t) (e2 : FuncExpr.t) : FuncExpr.t option =
    let p1 =
      collect_root_path forest.graph e1
      |> CCList.flat_map (fun (src, _, dst) -> [ src; dst ])
      |> TermSet.of_list
    in
    let p2 =
      collect_root_path forest.graph e2
      |> CCList.flat_map (fun (src, _, dst) -> [ src; dst ])
      |> TermSet.of_list
    in
    let intersection = TermSet.inter p1 p2 in
    TermSet.to_list intersection
    |> CCList.sort (fun x y ->
           let rx = TermMap.find x forest.ranks in
           let ry = TermMap.find y forest.ranks in
           CCInt.compare rx ry)
    |> CCList.head_opt

  let rec path_from_to (forest : G.t) (src : FuncExpr.t) (tgt_dst : FuncExpr.t)
      : G.edge list option =
    if FuncExpr.equal src tgt_dst then Some []
    else
      let succ = G.succ_e forest src in
      CCList.fold_left
        (fun acc (src, lbl, dst) ->
          CCOption.or_
            ~else_:
              (path_from_to forest dst tgt_dst
              |> CCOption.map (fun pth -> (src, lbl, dst) :: pth))
            acc)
        None succ

  let explain (forest : t) (e1 : FuncExpr.t) (e2 : FuncExpr.t) :
      (FuncExpr.t * FuncExpr.t) list =
    let target = lca forest e1 e2 in
    CCOption.map
      (fun tgt ->
        let e1s = path_from_to forest.graph e1 tgt |> Option.get in
        let e2s = path_from_to forest.graph e2 tgt |> Option.get in
        CCList.append e1s e2s |> CCList.map (fun (_, lbl, _) -> lbl))
      target
    |> CCOption.get_or ~default:CCList.empty
end

type congruence_implied_by_set = L.t UnionToLit.t

module TermUF = UnionFind.Make (FuncExpr)
module EqSet = CCSet.Make (L.A)

type state = {
  to_assign_pos_lits : L.A.t list;
  congruence_classes : TermUF.store;
  proof_forest : ProofForest.t;
  formula : TermGraph.t;
  cause_lookup : congruence_implied_by_set;
  negated : (FuncExpr.t * FuncExpr.t) list;
  term_to_id : int TermMap.t;
}

type theory_state = state

module SolverStateM = StateMonad.Make (struct
  type t = state
  type state = t
end)

module M = SolverStateM

let lift_uf_monad (m : 'a TermUF.UFMonad.t) : 'a SolverStateM.t =
  SolverStateM.Syntax.(
    let* (full_state : state) = SolverStateM.get in
    let v, new_uf = m full_state.congruence_classes in
    let nst = { full_state with congruence_classes = new_uf } in
    SolverStateM.map (SolverStateM.set nst) (fun _ -> v))

let lookup_term_ref (t : FuncExpr.t) : TermUF.rref SolverStateM.t =
  SolverStateM.Syntax.(
    let* cur_state = SolverStateM.get in
    let el_ref = TermMap.find t cur_state.term_to_id in
    let m = TermUF.find_repr el_ref in
    let* maybe_res = lift_uf_monad m in
    match maybe_res with
    | None -> lift_uf_monad (TermUF.make t)
    | Some i -> SolverStateM.return i)

let lookup_term (t : FuncExpr.t) : FuncExpr.t SolverStateM.t =
  SolverStateM.Syntax.(
    let* found = lookup_term_ref t in
    let* r = lift_uf_monad (TermUF.val_of_ref found) in
    SolverStateM.return (Option.get r))

let unify_terms (x : FuncExpr.t) (y : FuncExpr.t) : FuncExpr.t SolverStateM.t =
  SolverStateM.Syntax.(
    let* f = lookup_term_ref x in
    let* g = lookup_term_ref y in
    let* repr_nd = lift_uf_monad (TermUF.union f g) in
    if Option.get repr_nd = f then SolverStateM.return x
    else SolverStateM.return y)

let congruent (x : FuncExpr.t) (y : FuncExpr.t) : bool SolverStateM.t =
  match (x, y) with
  | App { name = xname; args = xargs }, App { name = yname; args = yargs } ->
      SolverStateM.Syntax.(
        let* eq_args =
          SolverStateM.all_m
            (fun (xarg, yarg) ->
              let* rx = lookup_term_ref xarg in
              let* ry = lookup_term_ref yarg in
              SolverStateM.return (rx = ry))
            (CCList.combine xargs yargs)
        in
        SolverStateM.return (CCString.equal xname yname && eq_args))
  | _ -> SolverStateM.return false

let pred_set (x : FuncExpr.t) : TermSet.t SolverStateM.t =
  SolverStateM.Syntax.(
    let* repr = lookup_term_ref x in
    let* all_in_set = lift_uf_monad (TermUF.mems repr) in
    let* st = SolverStateM.get in
    let g = st.formula in
    SolverStateM.return
      (all_in_set |> CCList.flat_map (TermGraph.pred g) |> TermSet.of_list))

let rec merge_terms (acting_on_lit : L.t) (x : FuncExpr.t) (y : FuncExpr.t) :
    unit SolverStateM.t =
  SolverStateM.Syntax.(
    let* repr_x = lookup_term x in
    let* repr_y = lookup_term y in
    if not (FuncExpr.equal repr_x repr_y) then
      (* lookup all users that may now be congruent *)
      let* pred_x = pred_set x in
      let* pred_y = pred_set y in
      let prod =
        CCList.product
          (fun x y -> (x, y))
          (TermSet.to_list pred_x) (TermSet.to_list pred_y)
      in
      let* _ = unify_terms x y in
      let* st = SolverStateM.get in
      let update = ProofForest.apply_union st.proof_forest x y in
      let* _ = SolverStateM.set { st with proof_forest = update } in
      SolverStateM.fold_m
        (fun _ (x, y) ->
          let* xrepr = lookup_term x in
          let* yrepr = lookup_term y in
          let* is_congruent = congruent x y in
          if (not (FuncExpr.equal xrepr yrepr)) && is_congruent then
            merge_terms acting_on_lit xrepr yrepr
          else SolverStateM.return ())
        () prod
    else SolverStateM.return ())

let find_negative_consequence : (FuncExpr.t * FuncExpr.t) option SolverStateM.t
    =
  SolverStateM.Syntax.(
    let* st = SolverStateM.get in
    SolverStateM.fold_m
      (fun maybe_pr (el_x, el_y) ->
        let* rep1 = lookup_term_ref el_x in
        let* rep2 = lookup_term_ref el_y in
        let opt = CCOption.return_if (rep1 = rep2) (el_x, el_y) in
        CCOption.( <+> ) maybe_pr opt |> SolverStateM.return)
      None st.negated)

let fresh_eq_lits : L.A.t list SolverStateM.t =
  SolverStateM.Syntax.(
    let* st = SolverStateM.get in
    let is_now_eq (EqCons.Eq (x, y)) =
      let* rx = lookup_term_ref x in
      let* ry = lookup_term_ref y in
      SolverStateM.return (rx = ry)
    in
    let* not_eq =
      SolverStateM.filter_m
        (fun x -> SolverStateM.map (is_now_eq x) (fun y -> not y))
        st.to_assign_pos_lits
    in
    let* _ = SolverStateM.set { st with to_assign_pos_lits = not_eq } in
    SolverStateM.filter_m is_now_eq st.to_assign_pos_lits)

let explain_conflict ((e1, e2) : FuncExpr.t * FuncExpr.t) :
    L.t list SolverStateM.t =
  SolverStateM.Syntax.(
    let* st = SolverStateM.get in
    let explanation = ProofForest.explain st.proof_forest e1 e2 in
    (* so a total explanaton is the combination of the negative literal
       + positive examples*)
    let neg_ex = L.Neg (Eq (e1, e2)) in
    let pos_exs =
      CCList.map
        (fun exp ->
          CCOption.or_
            ~else_:(UnionToLit.find_opt (CCPair.swap exp) st.cause_lookup)
            (UnionToLit.find_opt exp st.cause_lookup)
          |> Option.get)
        explanation
    in
    SolverStateM.return (neg_ex :: pos_exs))

(* two cases:
   Neg then we need to add this to the neg set, do a consistency check. otherwise merge, then do a consistency check.*)
let set_true (cons : L.t) :
    [ `Conflict of L.t list | `Success of L.t list ] SolverStateM.t =
  SolverStateM.Syntax.(
    let* _ =
      match cons with
      | L.Pos (Eq (p, n)) -> merge_terms cons p n
      | L.Neg (Eq (p, n)) ->
          let* m = SolverStateM.get in
          let new_negated = (p, n) :: m.negated in
          SolverStateM.set { m with negated = new_negated }
    in
    let* maybe_conflict = find_negative_consequence in
    match maybe_conflict with
    | Some conf ->
        SolverStateM.map (explain_conflict conf) (fun x -> `Conflict x)
    | None ->
        SolverStateM.map fresh_eq_lits (fun x ->
            `Success (CCList.map (fun e -> L.Pos e) x)))

let rec init_cc_class (l : FuncExpr.t list) : unit TermUF.UFMonad.t =
  TermUF.UFMonad.Syntax.(
    match l with
    | [] -> TermUF.UFMonad.return ()
    | h :: tl ->
        let* _ = TermUF.make h in
        init_cc_class tl)

let initialize (cons : L.t list) : state =
  let atoms =
    CCList.map (fun x -> match x with L.Pos x -> x | L.Neg x -> x) cons
  in
  let term_set =
    atoms
    |> CCList.flat_map (fun x -> match x with EqCons.Eq (x, y) -> [ x; y ])
    |> CCList.map subterms |> union_list |> TermSet.to_list
  in
  let keyed = CCList.mapi (fun i t -> (t, i)) term_set |> TermMap.of_list in
  let _, cclass = (init_cc_class term_set) TermUF.emp in
  let all_pos =
    CCList.flat_map (function L.Neg _ -> [] | L.Pos l -> [ l ]) cons
  in
  {
    to_assign_pos_lits = all_pos;
    congruence_classes = cclass;
    formula = formula_to_term_graph atoms;
    proof_forest = ProofForest.empty;
    cause_lookup = UnionToLit.empty;
    term_to_id = keyed;
    negated = CCList.empty;
  }

(*
type state = fexpr UnionFind.store 
*)
