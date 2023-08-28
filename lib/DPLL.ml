
module Model(L: CCMap.OrderedType) = struct 
  module Map =  CCMap.Make(L)
  type t = bool Map.t
end




(* to make dpll mildly effecient we need to side effect clauses *)



module SolverState(L: Formula.LiteralSymbol) = struct 
  module F = Formula.Make(L)
  module LitSet = CCSet.Make(F.Literal)

  module Clause(L: Formula.LiteralSymbol) = struct
    type state = {active: bool; watched: LitSet.t; cl: F.clause}
    type t = state ref
  
    let assign_true (clause: t) = 
      clause := {!clause with active = false}
      
    let activate (clause: t) = 
      clause := {!clause with active = true}
  
    let is_active (clause: t) = 
      !clause.active
  end

  
  module M = Model(L)
  module OccM = CCMap.Make(F.Literal)
  module SymbSet = Set.Make(L)
  
  module Clauses = Clause(L)

  type t_watch_list = (Clauses.t list) OccM.t

  type assignment_type = 
    | Dec
    | Consequence

  type assignment = {target: F.Literal.t ; kind: assignment_type}

  type t = {watch_lists: t_watch_list; formula: Clauses.t list; model: M.t;
   occ_clause:  (Clauses.t list) OccM.t; 
   (* obviously bad *)
   unassigned: SymbSet.t;
   stack: (assignment *  Clauses.t list) list
   }

  let assign_true_in_state (st: t) (l: assignment) = 
    let unassigned = SymbSet.remove (F.Literal.symbol l.target) st.unassigned in 
    let assigned = M.Map.add (F.Literal.symbol l.target) (F.Literal.value l.target) st.model in
    let affected_clauses = OccM.find l.target st.occ_clause |> CCList.filter (Clauses.is_active) in
    let rstack = (l, affected_clauses) :: st.stack in
    CCList.iter (Clauses.assign_true) affected_clauses; 
      {watch_lists = st.watch_lists; formula = st.formula; 
      model = assigned; unassigned = unassigned; stack = rstack; occ_clause = st.occ_clause} 

  type reduction_result =
    | Conflict
    | Result of t

  
  let update_watcher (cls: Clauses.t) (st: t) (curr_to_assign: LitSet.t): (t *  LitSet.t) option = 
    let next_unassigned = CCList.filter (fun lit -> F.Literal.is_non_false lit (fun x -> M.Map.get x st.model)) !cls.cl in
    let len = CCList.length next_unassigned in
    if len = 0 then None else
      if len = 1 then Some(st, LitSet.union (LitSet.of_list next_unassigned) curr_to_assign) 
      else 
        let to_watch = CCList.take 2 next_unassigned in
        let new_watching = CCList.fold_left (fun (curr_watch: t_watch_list) (lit:OccM.key)  -> 
          OccM.add lit (cls :: (OccM.find lit curr_watch )) curr_watch) st.watch_lists to_watch in
        cls := {!cls with watched=LitSet.of_list to_watch};Some({st with watch_lists=new_watching},curr_to_assign)


  (*returns a conflict/result alogn with the identified unit clauses*)
  let rec unit_prop_aux (st: t) (just_assigned: F.Literal.t) (to_assign: LitSet.t): reduction_result  = 
    let target_of_clause_update = (F.Literal.neg just_assigned) in
    (* collect all active clauses watching this literal*)
    let watching_clauses = OccM.find target_of_clause_update st.watch_lists in
    (* for each clause attempt to update the watch literals, if empty conflict, else continue*)
    let (active_watchers, inactive_watchers) = CCList.partition (Clauses.is_active) watching_clauses in
    (* mantain the watch list of inactive clauses so that they still have watch variables if they become active *)
    let init_watch = OccM.add just_assigned inactive_watchers st.watch_lists in 
    let maybe_reduced_state = CCList.fold_left (fun (curr_st: (t *  LitSet.t) option) cls 
      -> CCOption.flat_map (fun (st, curr_set) -> update_watcher cls st curr_set) curr_st) (Some({st with watch_lists = init_watch},to_assign)) active_watchers in
    match maybe_reduced_state with
    | None -> Conflict
    | Some(st,assignees) ->
      if LitSet.is_empty assignees then Result st else
        let next_assign = LitSet.choose assignees in 
        let setr = LitSet.remove next_assign assignees in 
        unit_prop_aux st next_assign setr

  let unit_prop (st: t) (just_assigned: F.Literal.t): reduction_result = 
    unit_prop_aux st just_assigned LitSet.empty

  let assign_true (st: t) (l: assignment): t = 
    assign_true_in_state st l

    

  let undo_literal_assignment (st:t) (l: F.Literal.t) (to_undo_clauses: Clauses.t list): t = 
    let m = M.Map.remove (F.Literal.symbol l) st.model in
    let u = SymbSet.add (F.Literal.symbol l) st.unassigned in
    CCList.iter (Clauses.activate) to_undo_clauses;
    {st with model = m; unassigned = u}

  (* recursively undo this assingment, this involves reactivating the affected clauses
    adding the literal to the unassigned list, removing it from the model
    and if there is Dec then we pop indicating the last decision
    if we never reach a decision point then we have exhausted the model possibilities and None->unsat*)
  let rec backtrack (st: t): (t * F.Literal.t)  option = 
    match st.stack with 
    | [] -> None
    | (a,to_undo_clauses) :: rst_stack ->
        let up = {st with stack = rst_stack} in
        let undid_value = undo_literal_assignment up a.target to_undo_clauses in
        match a.kind with 
        | Dec -> Some (undid_value, a.target)
        | Consequence -> backtrack undid_value
  

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
          CCOption.flat_map (fun (nst, js) -> sol_to_opt (solve (assign_true_in_state nst {target=js; kind=Consequence})  (Some js))) (backtrack st)
        | Result nt -> Some nt) just_assigned in
    CCOption.get_or ~default:`Unsat (CCOption.map (fun st ->
    match (SymbSet.choose_opt st.unassigned)  with 
      (* if everything is assigned we are done *)
      | None -> `Sat st
      (* if not we arbitrarily assign to true
         do unit propogation until we 
    and solve from there *)
      | Some target_assignment ->
        let lit = F.Literal.Pos target_assignment in 
        solve (assign_true_in_state st {target=lit; kind=Dec}) (Some lit)) next_state)



end