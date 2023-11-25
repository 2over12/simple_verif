module type X = sig
  include CCMap.OrderedType

  val pp : Format.formatter -> t -> unit
end

module Model (L : X) = struct
  module ModelMap = CCMap.Make (L)

  type t = bool ModelMap.t

  let show (x : t) =
    Format.flush_str_formatter () |> ignore;
    (ModelMap.pp L.pp CCBool.pp) Format.str_formatter x;
    Format.flush_str_formatter ()
end

(* to make dpll mildly effecient we need to side effect clauses *)

module SolverState (T : Theory.S) = struct
  module F = Formula.Make (T.L)
  module LitSet = CCSet.Make (T.L)

  module Clauses = struct
    type state = { active : bool; watched : LitSet.t; cl : F.clause }
    type t = state ref

    let assign_true (clause : t) = clause := { !clause with active = false }
    let activate (clause : t) = clause := { !clause with active = true }
    let is_active (clause : t) = !clause.active
  end

  module M = Model (T.L.A)
  module OccM = CCMap.Make (T.L)
  module SymbSet = Set.Make (T.L.A)

  type t_watch_list = Clauses.t list OccM.t
  type assignment_type = Dec of T.theory_state | Consequence
  type assignment = { target : T.L.t; kind : assignment_type }

  type t = {
    watch_lists : t_watch_list;
    formula : Clauses.t list;
    model : M.t;
    occ_clause : Clauses.t list OccM.t;
    (* obviously bad *)
    unassigned : SymbSet.t;
    stack : (assignment * Clauses.t list) list;
    theory_state : T.theory_state;
  }

  let assign_true_in_state (st : t) (l : assignment) =
    let unassigned = SymbSet.remove (F.Literal.symbol l.target) st.unassigned in
    let assigned =
      M.ModelMap.add
        (F.Literal.symbol l.target)
        (F.Literal.value l.target) st.model
    in
    let affected_clauses =
      OccM.find l.target st.occ_clause |> CCList.filter Clauses.is_active
    in
    let rstack = (l, affected_clauses) :: st.stack in
    CCList.iter Clauses.assign_true affected_clauses;
    {
      watch_lists = st.watch_lists;
      formula = st.formula;
      model = assigned;
      unassigned;
      stack = rstack;
      occ_clause = st.occ_clause;
      theory_state = st.theory_state;
    }

  type reduction_result = TheoryConflict of LitSet.t | Conflict | Result of t

  let update_watcher (cls : Clauses.t) (st : t) (curr_to_assign : LitSet.t) :
      (t * LitSet.t) option =
    let next_unassigned =
      CCList.filter
        (fun lit ->
          F.Literal.is_non_false lit (fun x -> M.ModelMap.get x st.model))
        !cls.cl
    in
    let len = CCList.length next_unassigned in
    if len = 0 then None
    else if len = 1 then
      Some (st, LitSet.union (LitSet.of_list next_unassigned) curr_to_assign)
    else
      let to_watch = CCList.take 2 next_unassigned in
      let new_watching =
        CCList.fold_left
          (fun (curr_watch : t_watch_list) (lit : OccM.key) ->
            OccM.add lit (cls :: OccM.find lit curr_watch) curr_watch)
          st.watch_lists to_watch
      in
      cls := { !cls with watched = LitSet.of_list to_watch };
      Some ({ st with watch_lists = new_watching }, curr_to_assign)

  let perform_theory_update (st : T.theory_state) (just_assigned : T.L.t) :
      [ `Implied of LitSet.t * T.theory_state | `Conflict of LitSet.t ] =
    let v, nst = T.set_true just_assigned st in
    match v with
    | `Conflict conflicts -> `Conflict (conflicts |> LitSet.of_list)
    | `Success implied -> `Implied (implied |> LitSet.of_list, nst)

  (*returns a conflict/result alogn with the identified unit clauses*)
  let rec unit_prop_aux (st : t) (just_assigned : T.L.t) (to_assign : LitSet.t)
      : reduction_result =
    (*first we ask the theory to set the lit to true if we get a conflict we are inconsistent, otherwise we may have some additional info to prop *)
    match perform_theory_update st.theory_state just_assigned with
    | `Implied (implied_lits, nst) -> (
        let to_assign = LitSet.union to_assign implied_lits in
        let st = { st with theory_state = nst } in
        let target_of_clause_update = F.Literal.neg just_assigned in
        (* collect all active clauses watching this literal*)
        let watching_clauses =
          OccM.find target_of_clause_update st.watch_lists
        in
        (* for each clause attempt to update the watch literals, if empty conflict, else continue*)
        let active_watchers, inactive_watchers =
          CCList.partition Clauses.is_active watching_clauses
        in
        (* mantain the watch list of inactive clauses so that they still have watch variables if they become active *)
        let init_watch =
          OccM.add just_assigned inactive_watchers st.watch_lists
        in
        let maybe_reduced_state =
          CCList.fold_left
            (fun (curr_st : (t * LitSet.t) option) cls ->
              CCOption.flat_map
                (fun (st, curr_set) -> update_watcher cls st curr_set)
                curr_st)
            (Some ({ st with watch_lists = init_watch }, to_assign))
            active_watchers
        in
        match maybe_reduced_state with
        | None -> Conflict
        | Some (st, assignees) ->
            if LitSet.is_empty assignees then Result st
            else
              let next_assign = LitSet.choose assignees in
              let setr = LitSet.remove next_assign assignees in
              let st =
                assign_true_in_state st
                  { target = next_assign; kind = Consequence }
              in
              unit_prop_aux st next_assign setr)
    | `Conflict l -> TheoryConflict l

  let unit_prop (st : t) (just_assigned : T.L.t) : reduction_result =
    unit_prop_aux st just_assigned LitSet.empty

  let assign_true (st : t) (l : assignment) : t = assign_true_in_state st l

  let undo_literal_assignment (st : t) (l : T.L.t)
      (to_undo_clauses : Clauses.t list) : t =
    let m = M.ModelMap.remove (F.Literal.symbol l) st.model in
    let u = SymbSet.add (F.Literal.symbol l) st.unassigned in
    CCList.iter Clauses.activate to_undo_clauses;
    { st with model = m; unassigned = u }

  (* recursively undo this assingment, this involves reactivating the affected clauses
     adding the literal to the unassigned list, removing it from the model
     and if there is Dec then we pop indicating the last decision
     if we never reach a decision point then we have exhausted the model possibilities and None->unsat*)
  let rec backtrack (st : t) : (t * T.L.t) option =
    match st.stack with
    | [] -> None
    | (a, to_undo_clauses) :: rst_stack -> (
        let up = { st with stack = rst_stack } in
        let undid_value = undo_literal_assignment up a.target to_undo_clauses in
        match a.kind with
        | Dec tstate ->
            Some ({ undid_value with theory_state = tstate }, a.target)
        | Consequence -> backtrack undid_value)

  let sol_to_opt (sol : [ `Sat of t | `Unsat ]) =
    match sol with `Sat x -> Some x | `Unsat -> None

  let add_clause_to_state (st : t) (watch_list : LitSet.t) (clause : LitSet.t) :
      t =
    let dedup = LitSet.to_list clause in
    let cls =
      {
        Clauses.active = true;
        Clauses.cl = dedup;
        Clauses.watched = watch_list;
      }
      |> ref
    in
    let new_bindings =
      CCList.map (fun l -> (l, cls :: OccM.find l st.occ_clause)) dedup
    in
    let new_occ = OccM.add_list st.occ_clause new_bindings in
    let new_watcher_bindings =
      CCList.map
        (fun l -> (l, cls :: OccM.find l st.watch_lists))
        (LitSet.to_list watch_list)
    in
    let new_watchers = OccM.add_list st.watch_lists new_watcher_bindings in
    {
      stack = st.stack;
      theory_state = st.theory_state;
      formula = cls :: st.formula;
      unassigned = st.unassigned;
      model = st.model;
      watch_lists = new_watchers;
      occ_clause = new_occ;
    }

  (* so for defensive programming there's three scenarios that could happen here:
     the only time it is safe to backtrack is if we can prove that *)
  let attempt_create_info_clause (st : t) (lset : LitSet.t) : t option =
    let still_has_conflict =
      LitSet.for_all
        (fun x ->
          F.Literal.is_definitely_true x (fun el -> M.ModelMap.get el st.model))
        lset
    in
    let flipped_to_things_we_want =
      LitSet.map (fun x -> F.Literal.neg x) lset
    in
    let unassigned_2 =
      LitSet.filter
        (fun x -> not (SymbSet.mem (F.Literal.symbol x) st.unassigned))
        flipped_to_things_we_want
      |> LitSet.to_list |> CCList.take 2
    in
    if CCList.length unassigned_2 = 2 then
      (*build new clause and add it*)
      Some
        (add_clause_to_state st
           (LitSet.of_list unassigned_2)
           flipped_to_things_we_want)
    else if still_has_conflict then
      (*we still have a conflict so we can backtrack*)
      None
    else Some st

  let rec solve (st : t) (just_assigned : T.L.t option) : [ `Sat of t | `Unsat ]
      =
    (* obviously bad to choose an arbitrary literal.. todo CDCL*)
    (* also not doing unit clause detection currently... *)
    (* first if we have an assignment do unit prop, if we are stuck then backtrack restart solve from that state
       , else we have a decision to make*)
    let next_state =
      if CCOption.is_none just_assigned then Some st
      else
        CCOption.flat_map
          (fun to_reduce ->
            match unit_prop st to_reduce with
            | TheoryConflict conflicting_vars ->
                conflict_backtracing conflicting_vars st
            | Conflict -> conflict_backtracing LitSet.empty st
            | Result nt -> Some nt)
          just_assigned
    in
    CCOption.get_or ~default:`Unsat
      (CCOption.map
         (fun st ->
           match SymbSet.choose_opt st.unassigned with
           (* if everything is assigned we are done *)
           | None -> `Sat st
           (* if not we arbitrarily assign to true
                   do unit propogation until we
              and solve from there *)
           | Some target_assignment ->
               let lit = T.L.Pos target_assignment in
               solve
                 (assign_true_in_state st
                    { target = lit; kind = Dec st.theory_state })
                 (Some lit))
         next_state)

  and
      (* Invariant since if there was a cnflict we should have discovered it prior to our decision
         this *)
      conflict_backtracing (conflicting_literals : LitSet.t) (st : t) : t option
      =
    let rec backtrack_until_theory_consistent (st : t) =
      let backtraced_state = backtrack st in
      match backtraced_state with
      | None -> None
      | Some (nst, dec_lit) -> (
          if LitSet.is_empty conflicting_literals then Some (nst, dec_lit)
          else
            match attempt_create_info_clause nst conflicting_literals with
            | Some st_with_conf -> Some (st_with_conf, dec_lit)
            | None -> backtrack_until_theory_consistent nst)
    in
    let backtraced_state = backtrack_until_theory_consistent st in
    CCOption.flat_map
      (fun (nst, js) ->
        let flip_dec = F.Literal.neg js in
        sol_to_opt
          (solve
             (assign_true_in_state nst
                { target = flip_dec; kind = Consequence })
             (Some flip_dec)))
      backtraced_state

  let solve_inject (f : F.cnf_formula) : [ `Sat of t | `Unsat ] =
    let stk = CCList.empty in
    let clauses : Clauses.t list =
      CCList.map
        (fun c ->
          let dedup = CCList.sort_uniq ~cmp:T.L.compare c in
          {
            Clauses.active = true;
            Clauses.cl = dedup;
            Clauses.watched = CCList.take 2 dedup |> LitSet.of_list;
          }
          |> ref)
        f
    in
    let unassigned_set =
      CCList.flat_map (fun ct -> !ct.Clauses.cl) clauses
      |> CCList.map (fun l -> F.Literal.symbol l)
      |> SymbSet.of_list
    in
    let cm = M.ModelMap.empty in
    let all_possible_lits =
      SymbSet.to_list unassigned_set
      |> CCList.flat_map (fun s -> [ T.L.Neg s; T.L.Pos s ])
    in
    let empty_occ_map = all_possible_lits |> CCList.map (fun l -> (l, [])) in
    let occ_map =
      List.append
        (CCList.flat_map
           (fun ct -> CCList.map (fun l -> (l, [ ct ])) !ct.Clauses.cl)
           clauses)
        empty_occ_map
      |> OccM.of_list_with ~f:(fun _ a b -> List.append a b)
    in
    let watch_list_non_empties =
      CCList.flat_map
        (fun ct ->
          CCList.map
            (fun l -> (l, [ ct ]))
            (!ct.Clauses.watched |> LitSet.to_list))
        clauses
      |> OccM.of_list_with ~f:(fun _ a b -> List.append a b)
    in
    let covered = OccM.keys watch_list_non_empties |> LitSet.of_iter in
    let empties =
      all_possible_lits |> CCList.filter (fun l -> not (LitSet.mem l covered))
    in
    let empt_list = empties |> CCList.map (fun l -> (l, [])) in
    let init_watc_list = OccM.add_list watch_list_non_empties empt_list in
    let init_st =
      {
        watch_lists = init_watc_list;
        occ_clause = occ_map;
        formula = clauses;
        stack = stk;
        model = cm;
        unassigned = unassigned_set;
        theory_state = T.initialize all_possible_lits;
      }
    in
    solve init_st None
end
