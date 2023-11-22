
module M = CCMap.Make(CCInt)

type rank = 
  | R of int

type 'a content = 
  | Link of int * 'a
  | Root of rank  * 'a




type 'a store = {members: 'a content M.t; next_address: int}



let make (x: 'a): (int, 'a store) StateMonad.t = 
    fun (st: 'a store) ->
        let curr = Root (R 0, x) in
        let mems = M.add st.next_address curr st.members in
        (st.next_address, {members=mems; next_address=st.next_address + 1})


let opt_t (m: ('a, 'b) StateMonad.t option) = 
  match m with 
    | Some nm -> 
      StateMonad.map nm (fun v -> Some v)
    | None -> fun (st: 'b) -> (None, st)

(* TODO: this isn't effecient at all, rec monad too *)
let rec find_repr (x: int): (int option, 'a store) StateMonad.t = 
  fun (st: 'a store) -> 
    let elem = M.find_opt x st.members in
    let (v, nst ) = (CCOption.map (fun cont ->
    match cont with 
      | Link (i, v) -> 
          StateMonad.Synax.(
            let* par = find_repr i in 
              match par with 
                | None -> StateMonad.return None
                | Some el -> let state_with_parent_updated = M.add x (Link (el,v) ) st.members in
                  StateMonad.map (StateMonad.set {members=state_with_parent_updated; next_address=st.next_address}) (fun _ -> Some el)
          )
      | Root (_, v) ->
        (* we are going to update children so update our rank to 1, inv: 
           if we got here we must have children because we came from somewhere *)
        let new_map = M.add x (Root(R 1, v)) st.members in
          StateMonad.map (StateMonad.set {members=new_map; next_address=st.next_address}) (fun _ -> (Some x))
    ) elem |> opt_t) st in
    (CCOption.flatten v , nst)


let rank_of (x: 'a content): int = 
    match x with 
      | Root (R r, _) -> r
      | _ -> raise (Failure "rank of on non root")

let value_of (x: 'a content): 'a = 
    match x with 
      | Root (_, v) -> v
      | Link (_, v) -> v

      
let node_info (ind_1: int) (ind_2: int) (r1:int) (r2: int) (v1: 'a) (v2: 'a) (nrank:int):
  (int*int* 'a content * 'a content) = 
  (if r1 > r2 then (ind_1, ind_2, Root (R nrank, v1), Link (ind_1, v2)) 
    else (ind_2, ind_1, Root (R nrank, v2), Link (ind_2, v1))) 


let  update_state (sx:int option) (sy:int option) (st: 'a store): (int option, 'a store) StateMonad.t = 
    match (sx,sy) with 
      | (Some x, Some y) ->
        (let (maybe_root: (int, 'a store) StateMonad.t option) = (CCOption.map2 (fun x_el y_el ->
          let r1 = rank_of x_el in 
          let v1 = value_of x_el in
          let r2 = rank_of y_el in
          let v2 = value_of y_el in
          let nrank = r1 + r2 in
          let (repr, child, repr_node, child_node) = node_info x y r1 r2 v1 v2 nrank in 
          let st_with_new_repr = M.add repr repr_node st.members in
          let st_with_child = M.add  child child_node st_with_new_repr in
          StateMonad.map  (StateMonad.set {members=st_with_child;next_address=st.next_address}) 
            (fun _ -> repr)
          ) (M.find_opt x st.members) (M.find_opt y st.members)) in maybe_root |> opt_t)
      | _ -> (StateMonad.return None)

let union (x: int) (y: int): (int option, 'a store) StateMonad.t = 
    StateMonad.Synax.(
      let* sx = find_repr x in
      let* sy = find_repr y in
      let* st = StateMonad.get in
        update_state sx sy st 
    )

let emp: 'a store = {members=M.empty; next_address=0}

