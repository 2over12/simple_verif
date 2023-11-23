

module type Atom = sig
    type t
    val pp: Format.formatter -> t -> unit
    include CCMap.OrderedType with type t := t
end

module type Literals = sig
    module A: Atom

    
    
    type t = 
    | Neg of A.t
    | Pos of A.t
    [@@deriving eq, ord,show]
  

end

module type S = sig 
module L: Literals
type state

val initialize: L.t list -> state
val set_true:  L.t -> ([`Conflict of  L.t list | `Success of  L.t list ], state) StateMonad.t
val retract_literal:  L.t ->  (unit, state) StateMonad.t
end