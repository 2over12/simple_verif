module type T = sig
  type t
end

module type S = sig
  type 'a t

  val map : 'a t -> ('a -> 'b) -> 'b t

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  val fold_m : ('b -> 'a -> 'b t) -> 'b -> 'a list -> 'b t
  val all_m : ('a -> bool t) -> 'a list -> bool t
  val filter_m : ('a -> bool t) -> 'a list -> 'a list t
end

module type Monad = sig
  type 'a t

  val flatmap : 'a t -> ('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
end

module Make (M : Monad) : S with type 'a t := 'a M.t = struct
  let map (m : 'a M.t) (f : 'a -> 'b) = M.flatmap m (fun x -> M.return (f x))

  module Syntax = struct
    let ( let* ) = M.flatmap
  end

  let rec fold_m (f : 'b -> 'a -> 'b M.t) (init : 'b) (l : 'a list) : 'b M.t =
    match l with
    | [] -> M.return init
    | h :: tl ->
        Syntax.(
          let* prev_result = fold_m f init tl in
          f prev_result h)

  let all_m (f : 'a -> bool M.t) (l : 'a list) : bool M.t =
    fold_m
      (fun pbool cur_elem ->
        Syntax.(
          let* rb = f cur_elem in
          M.return (pbool && rb)))
      true l

  let filter_m (f : 'a -> bool M.t) (l : 'a list) : 'a list M.t =
    fold_m
      (fun tot el ->
        M.flatmap (f el) (fun b ->
            if b then M.return (el :: tot) else M.return tot))
      [] l
end
