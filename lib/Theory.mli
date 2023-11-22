



type atom
type state

type literal = 
| Neg of atom
| Pos of atom
[@@deriving eq, ord]

val initialize: literal list -> state
val set_true: literal -> ([`Conflict of literal list | `Success of literal list ], state) StateMonad.t
val retract_literal: literal ->  (unit, state) StateMonad.t