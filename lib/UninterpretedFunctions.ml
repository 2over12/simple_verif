open Ppx_hash_lib.Std
open Hash.Builtin

module FuncExpr = struct
  type t = App of { name : string; args : t list } | Var of string
  [@@deriving eq, ord, hash, show]
end

module L = struct
  module A = struct
    type t = Eq of FuncExpr.t * FuncExpr.t [@@deriving eq, ord, show]

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

module ProofForest =
  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (FuncExpr) (ProofLabel)

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
  CCList.flat_map (fun x -> match x with L.A.Eq (x, y) -> [ x; y ]) form
  |> term_to_term_graph

module UnionToLit = Map.Make (struct
  type t = FuncExpr.t * FuncExpr.t

  let compare = CCPair.compare FuncExpr.compare FuncExpr.compare
end)

module TermMap = Map.Make (FuncExpr)

type congruence_implied_by_set = FuncExpr.t UnionToLit.t

module TermUF = UnionFind.Make (FuncExpr)

type state = {
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

let rec merge_terms (x : FuncExpr.t) (y : FuncExpr.t) : unit SolverStateM.t =
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
      SolverStateM.fold_m
        (fun _ (x, y) ->
          let* xrepr = lookup_term x in
          let* yrepr = lookup_term y in
          let* is_congruent = congruent x y in
          if (not (FuncExpr.equal xrepr yrepr)) && is_congruent then
            merge_terms xrepr yrepr
          else SolverStateM.return ())
        () prod
    else SolverStateM.return ())

(* two cases:
   Neg then we need to add this to the neg set, do a consistency check. otherwise merge, then do a consistency check.*)
let set_true (cons : L.t) :
    [ `Conflict of L.t list | `Success of L.t list ] SolverStateM.t =
  SolverStateM.Syntax.(
    let* st =
      match cons with
      | L.Pos (L.A.Eq (p, n)) -> merge_terms p n
      | L.Neg (L.A.Eq (p, n)) ->
          let* m = SolverStateM.get in
          let new_negated = (p, n) :: m.negated in
          SolverStateM.set { m with negated = new_negated }
    in
    raise (Failure ""))

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
    |> CCList.flat_map (fun x -> match x with L.A.Eq (x, y) -> [ x; y ])
    |> CCList.map subterms |> union_list |> TermSet.to_list
  in
  let keyed = CCList.mapi (fun i t -> (t, i)) term_set |> TermMap.of_list in
  let _, cclass = (init_cc_class term_set) TermUF.emp in
  {
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
