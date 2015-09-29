(* only expected to be 0, 1, 2; 2 represents undef *)
type vbit = int
type number = int64 (*Actually needs to be big_int_z but I forget the incantation for that right now*)

type value =
  | Vvector of vbit array * int * bool
  | VvectorR of value array * int * bool
  | Vregister of vbit array * int * bool * (string * (int * int)) list
  | Vundef (*For a few circumstances of undefined registers in VvectorRs built with sparse vectors*)

let to_bool = function
  | 0 -> false
  | 1 -> true
  | _ -> assert false

let get_barray  = function
  | Vvector(a,_,_) 
  | Vregister(a,_,_,_) -> a
  | _ -> assert false

let get_varray = function
  | VvectorR(a,_,_) -> a
  | _ -> assert false

let vector_access v n = match v with
  | VvectorR(array,start,is_inc) ->
    if is_inc
    then array.(n-start)
    else array.(start-n)
  | _ -> assert false
      
let bit_vector_access v n = match v with
  | Vvector(array,start,is_inc) | Vregister(array,start,is_inc,_) ->
    if is_inc
    then array.(n-start)
    else array.(start-n)
  | _ -> assert false

let vector_subrange v n m =
  let builder array length offset default =
    let new_array = Array.make length default in
    begin
      for x = 0 to length-1
      do new_array.(x) <- array.(x+offset) 
      done;
      new_array
    end
  in
  match v with
  | VvectorR(array,start,is_inc) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    VvectorR(builder array length offset (VvectorR([||], 0, true)),n,is_inc)
  | Vvector(array,start,is_inc) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    Vvector(builder array length offset 0,n,is_inc)
  | Vregister(array,start,is_inc,fields) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    Vvector(builder array length offset 0,n,is_inc)
  | _ -> v
