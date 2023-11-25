module type S = sig
  type t
  type store
  type rref = int

  module UFMonad : module type of StateMonad.Make (struct
    type state = store
  end)

  val make : t -> rref UFMonad.t
  val union : rref -> rref -> rref option UFMonad.t
  val find_repr : rref -> rref option UFMonad.t
  val val_of_ref : rref -> t option UFMonad.t
  val mems : rref -> t list UFMonad.t
  val emp : store
end

module Make (T : MonadUtils.T) : S with type t = T.t
