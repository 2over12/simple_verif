
module Model(L: CCMap.OrderedType) = struct 
  type t = bool CCMap.Make(L).t
end

(* A watch  lists maps watched literals to clauses, 
   if we go and update a watched literal we can check for unit propogation  *)
module WatchLists(L: Formula.Literal) = struct 
  module Map = CCMap.Make(L)
  type t = (Formula.Make(L).clause list) Map.t
end


module SolverState(L: Formula.Literal) = struct 
  module F = Formula.Make(L)
  module WLs = WatchLists(L)
  module M = Model(L)
  module OccM = WLs.Map

  type clause_state = {active: bool; watched: (L.symb * L.symb); cl: F.clause}


  type t = {watch_lists: WLs.t; formula: clause_state; model: M.t;
   occ_clause: (F.clause list) OccM.t; }

  let unit_prop (st: t) (just_assigned_false: L.symb) = 
    let to_update = CCOption.get_or ~default:[] (WLs.Map.get just_assigned_false st.watch_lists) in
    to_update


end