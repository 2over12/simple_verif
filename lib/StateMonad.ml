type ('a, 'state) t = 'state -> 'a * 'state

let flatmap (m: ('a, 'state) t) (f: 'a -> ('b, 'state) t): ('b, 'state) t =
  fun st ->
      let (v, mid_state) = m st in
      f v mid_state 
        

module Synax = struct  
  let (let*) x f = flatmap x f
end

let return (x: 'a): ('a, 'state) t = fun (st: 'state) -> (x, st)

let map (m: ('a, 'state) t) (f: 'a -> 'b): ('b, 'state) t = 
    fun (st: 'state) -> let (v, s) = m st in (f v, s)

let set (st: 'state): (unit, 'state) t = 
  fun (_st: 'state) -> ((), st)

let get: ('state, 'state) t =  
  fun (st: 'state) -> (st, st)