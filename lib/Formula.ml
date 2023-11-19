
module type LiteralSymbol = sig

  type t

  include CCMap.OrderedType with type t := t

  val pp: Format.formatter -> t -> unit
end

module Make(L: LiteralSymbol) = struct 
  module Literal = struct 
    type t = 
      | Neg of L.t
      | Pos of L.t
      [@@deriving ord, show]

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
    let is_non_false (x: t) (f: L.t -> bool option): bool =
        f (symbol x) |> CCOption.map (fun interpretation -> Bool.equal interpretation (value x)) |>
          CCOption.get_or ~default:true 
  end

  type uc_formula = 
  | And of uc_formula * uc_formula
  | Or of uc_formula * uc_formula
  | Not of uc_formula
  | Var of L.t
  [@@deriving show]

  type nnf_formula =
    | NAnd of nnf_formula * nnf_formula
    | NOr of nnf_formula * nnf_formula
    | NLit of Literal.t
  [@@deriving show]

  let rec rewrite_to_nnf_acc (f: uc_formula) (negate: bool): nnf_formula = 
    match (f, negate) with
    | (And (x,y), true) -> NOr (rewrite_to_nnf_acc x true, rewrite_to_nnf_acc y true)
    | (And (x,y), false) -> NAnd (rewrite_to_nnf_acc x false, rewrite_to_nnf_acc y false)
    | (Or (x,y), true) -> NAnd (rewrite_to_nnf_acc x true, rewrite_to_nnf_acc y true)
    | (Or (x,y), false) -> NOr (rewrite_to_nnf_acc x false, rewrite_to_nnf_acc y false)
    | ((Var l), false) -> NLit (Literal.Pos l)
    |((Var l), true) -> NLit (Literal.Neg l)
    |((Not e), x) -> rewrite_to_nnf_acc e (not x)

  let rewrite_to_nnf (f: uc_formula): nnf_formula = rewrite_to_nnf_acc f false
  
  type clause = Literal.t list [@@deriving show]

  type cnf_formula = clause list [@@deriving show]

  let rec rewrite_to_cnf (f: nnf_formula): nnf_formula = 
    match f with 
      | NAnd (a, b) ->
          let ra = rewrite_to_cnf a in 
          let rb = rewrite_to_cnf b in 
            NAnd (ra, rb)
      | NOr (a, b) -> rewrite_to_cnf_or a b
      | NLit lit -> NLit lit
  and rewrite_to_cnf_or (e1: nnf_formula) (e2: nnf_formula): nnf_formula =
      let re1 = rewrite_to_cnf e1 in 
      let re2 = rewrite_to_cnf e2 in
        match (re1, re2) with 
        | (NAnd (f, g), NAnd (a, b)) -> NAnd (NAnd (NAnd ((NOr (f, a)), (NOr (f, b))), NOr (g, a)), NOr (g, b))
        | (NAnd (f, g), a) -> NAnd (NOr (f, a), NOr(g,a))
        | (a, NAnd (f, g)) -> NAnd (NOr (f, a), NOr(g,a))
        | (a, b) -> NOr (a, b)
  
  let rewrite_to_cnf_clauses (f: nnf_formula): cnf_formula = 
    let normalized = rewrite_to_cnf f in 
    let rec literals_of (f: nnf_formula): clause = 
        match f with 
        | NOr (a, b) -> List.append (literals_of a) (literals_of b)
        | NAnd _ -> raise (Failure "rewrites should not allow an And below an Or")
        | NLit l -> [l] in
    let rec acc (f: nnf_formula): cnf_formula =
      match f with 
      | NAnd (a, b) -> List.append (acc a) (acc b) 
      | NOr (a, b) -> [List.append (literals_of a) (literals_of b)]
      | NLit a -> [[a]]
    in 
      acc normalized

end
