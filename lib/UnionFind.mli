
type 'a store
type rref

val make: 'a -> (rref, 'a store) StateMonad.t
val union: rref -> rref -> (rref option, 'a store) StateMonad.t
val find_repr: rref -> (rref option, 'a store) StateMonad.t
val val_of_ref: rref -> ('b option, 'b store) StateMonad.t
val emp: 'a store