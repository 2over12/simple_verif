
module Model(L: CCMap.OrderedType) = struct 
  type t = bool CCMap.Make(L).t
end




(* to make dpll mildly effecient we need to side effect clauses *)
module Clause(L: Formula.Literal) = struct
  module F = Formula.Make(L)
  type state = {active: bool; watched: (L.symb * L.symb); cl: F.clause}
  type t = state ref

  let assign_true (clause: t) = 
    clause := {!clause with active = false}
end
(* A watch  lists maps watched literals to clauses, 
   if we go and update a watched literal we can check for unit propogation  *)
module WatchLists(L: Formula.Literal) = struct 
  module Map = CCMap.Make(L)
  type t = (Clause(L).t list) Map.t
end


module SolverState(L: Formula.Literal) = struct 
  module F = Formula.Make(L)
  module WLs = WatchLists(L)
  module M = Model(L)
  module OccM = WLs.Map
  module LitSet = Set.Make(L)
  module Clauses = Clause(L)

  type assignment_type = 
    | Dec
    | Consequence

  type assignment = {target: L.symb ; kind: assignment_type}

  type t = {watch_lists: WLs.t; formula: Clauses.t list; model: M.t;
   occ_clause:  (Clauses.t list) OccM.t; 
   (* obviously bad *)
   unassigned: LitSet.t;
   stack: assignment list
   }

  let assign_true (st: t) (l: assignment) = 
    let unassigned = LitSet.remove l.target st.unassigned in 
    let assigned = WLs.Map.add l.target true st.model in
    let affected_clauses = OccM.find l.target st.occ_clause in
    let rstack = l :: st.stack in
    CCList.iter (Clauses.assign_true) affected_clauses; 
      {watch_lists = st.watch_lists; formula = st.formula; 
      model = assigned; unassigned = unassigned; stack = rstack; occ_clause = st.occ_clause} 

  let solve (st: t): [`Sat of M.t | `Unsat] =
    (* obviously bad to choose an arbitrary literal.. todo CDCL*)
    match (LitSet.choose_opt st.unassigned)  with 
      (* if everything is assigned we are done *)
      | None -> `Sat st.model
      (* if not we arbitrarily assign to true
         do unit propogation until we 
      a. hit a conflict in which case we need 
      to backtrack this decision and try the other way 
      b. we run out of actions and we need to solve again*)
      | Some target_assignment ->
        raise (Failure "not implemented")



  let unit_prop (st: t) (just_assigned_false: L.symb) = 
    let to_update = CCOption.get_or ~default:[] (WLs.Map.get just_assigned_false st.watch_lists) in
    to_update


end