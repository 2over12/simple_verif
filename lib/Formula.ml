
module type LiteralSymbol = sig

  type t

  include CCMap.OrderedType with type t := t
end

module Make(L: LiteralSymbol) = struct 
  module Literal = struct 
    type t = 
      | Neg of L.t
      | Pos of L.t
      [@@deriving ord]

    let neg (x : t):t = 
      match x with 
        | Neg v -> Pos v
        | Pos v -> Neg v

    let symbol (x: t): L.t = 
      match x with 
      | Neg v -> v
      | Pos v -> v
    
    let value (x: t): bool = 
        match x with 
        | Neg _ -> false
        | Pos _ -> true
  end


  type nnf_formula =
    | And of nnf_formula * nnf_formula
    | Or of nnf_formula * nnf_formula
    | Lit of Literal.t


  type clause = Literal.t list

  type cnf_formula = clause list

end
