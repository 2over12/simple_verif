
module Model(L: CCMap.OrderedType) = struct 
  module Map =  CCMap.Make(L)
  type t = bool Map.t
end




(* to make dpll mildly effecient we need to side effect clauses *)
module Clause(L: Formula.LiteralSymbol) = struct
  module F = Formula.Make(L)
  type state = {active: bool; watched: (F.Literal.t * F.Literal.t); cl: F.clause}
  type t = state ref

  let assign_true (clause: t) = 
    clause := {!clause with active = false}

  let is_active (clause: t) = 
    !clause.active
end
(* A watch  lists maps watched literals to clauses, 
   if we go and update a watched literal we can check for unit propogation  *)
module WatchLists(L: Formula.LiteralSymbol) = struct 
  module Map = CCMap.Make(L)
  type t = (Clause(L).t list) Map.t
end


module SolverState(L: Formula.LiteralSymbol) = struct 
  module F = Formula.Make(L)
  module WLs = WatchLists(F.Literal)
  module M = Model(L)
  module OccM = CCMap.Make(F.Literal)
  module LitSet = Set.Make(L)
  module Clauses = Clause(L)

  type assignment_type = 
    | Dec
    | Consequence

  type assignment = {target: F.Literal.t ; kind: assignment_type}

  type t = {watch_lists: WLs.t; formula: Clauses.t list; model: M.t;
   occ_clause:  (Clauses.t list) OccM.t; 
   (* obviously bad *)
   unassigned: LitSet.t;
   stack: (assignment *  Clauses.t list) list
   }

  let assign_true_in_state (st: t) (l: assignment) = 
    let unassigned = LitSet.remove (F.Literal.symbol l.target) st.unassigned in 
    let assigned = M.Map.add (F.Literal.symbol l.target) (F.Literal.value l.target) st.model in
    let affected_clauses = OccM.find l.target st.occ_clause |> CCList.filter (Clauses.is_active) in
    let rstack = (l, affected_clauses) :: st.stack in
    CCList.iter (Clauses.assign_true) affected_clauses; 
      {watch_lists = st.watch_lists; formula = st.formula; 
      model = assigned; unassigned = unassigned; stack = rstack; occ_clause = st.occ_clause} 

  type reduction_result =
    | Conflict
    | Result of t

  
  let unit_prop (st: t) (just_assigned: F.Literal.t): reduction_result = 
    let target_of_clause_update = (F.Literal.neg just_assigned) in
    raise (Failure "not implemented")

  let assign_true (st: t) (l: assignment): t = 
    assign_true_in_state st l

  let backtrack (st: t): (t * F.Literal.t)  option = raise (Failure "not implemented")

  

  let sol_to_opt (sol: [`Sat of t | `Unsat]) = 
      match sol with 
        | `Sat x -> Some x
        | `Unsat -> None

  let rec solve (st: t) (just_assigned: F.Literal.t option): [`Sat of t | `Unsat] =
    (* obviously bad to choose an arbitrary literal.. todo CDCL*)
    (* also not doing unit clause detection currently... *)
    (* first if we have an assignment do unit prop, if we are stuck then backtrack restart solve from that state
       , else we have a decision to make*)
    let next_state = if (CCOption.is_none just_assigned) then Some st else CCOption.flat_map (fun to_reduce -> 
      match unit_prop st to_reduce with
        | Conflict -> 
          CCOption.flat_map (fun (nst, js) -> sol_to_opt (solve nst (Some js))) (backtrack st)
        | Result nt -> Some nt) just_assigned in
    CCOption.get_or ~default:`Unsat (CCOption.map (fun st ->
    match (LitSet.choose_opt st.unassigned)  with 
      (* if everything is assigned we are done *)
      | None -> `Sat st
      (* if not we arbitrarily assign to true
         do unit propogation until we 
    and solve from there *)
      | Some target_assignment ->
        let lit = F.Literal.Pos target_assignment in 
        solve (assign_true_in_state st {target=lit; kind=Dec}) (Some lit)) next_state)



end