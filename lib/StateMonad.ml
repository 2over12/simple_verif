module Make (S : sig
  type state
end) =
struct
  module M = struct
    type 'a t = S.state -> 'a * S.state

    let flatmap (m : 'a t) (f : 'a -> 'b t) : 'b t =
     fun st ->
      let v, mid_state = m st in
      f v mid_state

    let return (x : 'a) : 'a t = fun (st : S.state) -> (x, st)
  end
  (*module Synax = struct
      let ( let* ) x f = flatmap x f
    end



    let map (m : ('a, 'state) t) (f : 'a -> 'b) : ('b, 'state) t =
     fun (st : 'state) ->
      let v, s = m st in
      (f v, s)*)

  include MonadUtils.Make (M)
  include M

  let set (st : S.state) : unit t = fun (_st : S.state) -> ((), st)
  let get : S.state t = fun (st : S.state) -> (st, st)
end
