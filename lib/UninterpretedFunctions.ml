

(*type fexpr =
| App of {name: string; args: fexpr list}
| Var of string
[@@deriving eq, ord]


type eq_expr =
| Eq of fexpr * fexpr
| Neq of fexpr * fexpr
[@@deriving eq, ord]

type atom = eq_expr [@@deriving eq, ord]

type literal = 
| Neg of atom
| Pos of atom
[@@deriving eq, ord]

type state = fexpr UnionFind.store 
*)