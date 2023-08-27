
module type Literal = sig

  type symb

  include CCMap.OrderedType with type t = symb
end

module Make(L: Literal) = struct 
  type lit = 
    | Neg of L.symb
    | Pos of L.symb


  type nnf_formula =
    | And of nnf_formula * nnf_formula
    | Or of nnf_formula * nnf_formula
    | Lit of lit


  type clause = lit list

  type cnf_formula = clause list

end
