open Big_int_Z

(* only expected to be 0, 1, 2; 2 represents undef *)
type vbit = Vone | Vzero | Vundef
type number = Big_int_Z.big_int

type value =
  | Vvector of vbit array * int * bool
  | VvectorR of value array * int * bool
  | Vregister of vbit array * int * bool * (string * (int * int)) list
  | Vbit of vbit (*Mostly for Vundef in place of undefined register place holders*)

let to_bool = function
  | Vzero -> false
  | Vone  -> true
  | Vundef -> assert false

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
    VvectorR(builder array length offset (VvectorR([||], 0, is_inc)),n,is_inc)
  | Vvector(array,start,is_inc) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    Vvector(builder array length offset Vzero,n,is_inc)
  | Vregister(array,start,is_inc,fields) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    Vvector(builder array length offset Vzero,n,is_inc)
  | _ -> v

let vector_append l r =
  match l,r with
  | Vvector(arrayl,start,ord), Vvector(arrayr,_,_)
  | Vvector(arrayl,start,ord), Vregister(arrayr,_,_,_)
  | Vregister(arrayl,start,ord,_), Vvector(arrayr,_,_)
  | Vregister(arrayl,start,ord,_), Vregister(arrayr,_,_,_) ->
    Vvector(Array.append arrayl arrayr,start,ord)
  | VvectorR(arrayl,start,ord),VvectorR(arrayr,_,_) ->
    VvectorR(Array.append arrayl arrayr, start,ord)
  | _ -> Vbit Vundef

let has_undef = function
  | Vvector(array,_,_) | Vregister(array,_,_,_) ->
    let rec foreach i =
      if i <= Array.length array
      then
        if array.(i) = Vundef then true
        else foreach (i+1)
      else false in
    foreach 0
  | _ -> false

let most_significant = function
  | Vvector(array,_,_) | Vregister(array,_,_,_) -> array.(0)
  | _ -> assert false

let bitwise_not_bit = function
  | Vone -> Vzero
  | Vzero -> Vone
  | _ -> Vundef

let bitwise_not = function
  | Vvector(array,s,d) | Vregister(array,s,d,_) -> Vvector( Array.map bitwise_not_bit array,s,d)
  | _ -> assert false    

let unsigned = function
  | (Vvector(array,_,_) as v) | (Vregister(array,_,_,_) as v)->
    if has_undef v
    then assert false
    else
      let acc = ref zero_big_int in
      begin for i = (Array.length array) - 1 downto 0 do
          match array.(i) with
          | Vone -> acc := add_big_int !acc (power_int_positive_int 2 i)
          | _ -> ()
        done;
        !acc
    end
  | _ -> assert false

let signed v =
  match most_significant v with
  | Vone -> minus_big_int(add_int_big_int 1 (unsigned (bitwise_not v)))
  | Vzero -> unsigned v
  | _ -> assert false

let to_num sign = if sign then signed else unsigned
  
let two_big_int = big_int_of_int 2
let max_64u = pred_big_int (power_big two_big_int (big_int_of_int 64))
let max_64  = pred_big_int (power_big two_big_int (big_int_of_int 63))
let min_64  = minus_big_int (power_big two_big_int (big_int_of_int 63))
let max_32u = big_int_of_int 4294967295
let max_32  = big_int_of_int 2147483647
let min_32  = big_int_of_int (-2147483648)
let max_8   = big_int_of_int 127
let min_8   = big_int_of_int (-128)
let max_5   = big_int_of_int 31
let min_5   = big_int_of_int (-32)

let get_max_representable_in sign n = 
  if (n = 64) then match sign with | true -> max_64 | false -> max_64u
  else if (n=32) then match sign with | true -> max_32 | false -> max_32u
  else if (n=8) then max_8
  else if (n=5) then max_5
  else match sign with | true -> power_big two_big_int (pred_big_int (big_int_of_int n))
                       | false -> power_big two_big_int (big_int_of_int n)

let get_min_representable_in _ n = 
  if (n = 64) then min_64
  else if (n=32) then min_32
  else if (n=8) then min_8
  else if (n=5) then min_5
  else minus_big_int (power_big two_big_int (big_int_of_int n))



let rec divide_by_2 array i n =
  if i < 0 || eq_big_int n zero_big_int
  then array
  else let (quo,modu) = quomod_big_int n two_big_int in
    if eq_big_int modu unit_big_int
    then begin array.(i) <- Vone; divide_by_2 array (i-1) quo end
    else divide_by_2 array (i-1) quo

let rec add_one_bit array co i =
  if i < 0
  then array
  else match array.(i),co with
    | Vzero,false -> array.(i) <- Vone; array
    | Vzero,true  -> array.(i) <- Vone; add_one_bit array true (i-1)
    | Vone, false -> array.(i) <- Vzero; add_one_bit array true (i-1)
    | Vone, true  -> add_one_bit array true (i-1)
    | Vundef,_ -> assert false

let to_vec ord len n =
  let len = int_of_big_int len in
  let array = Array.make len Vzero in
  let start = if ord then 0 else len-1 in
  if eq_big_int n zero_big_int
  then Vvector(array, start, ord)
  else if gt_big_int n zero_big_int
  then Vvector(divide_by_2 array (len -1) n, start, ord)
  else
    let abs_n = abs_big_int n in
    let abs_array = divide_by_2 array (len-1) abs_n in
    let v_abs = bitwise_not (Vvector(abs_array,start,ord)) in
    match v_abs with
    | Vvector(array,start,ord) -> Vvector(add_one_bit array false (len-1),start,ord)
    | _ -> assert false

let to_vec_inc (len,n) = to_vec true len n
let to_vec_dec (len,n) = to_vec false len n

let length = function
  | Vvector(array,_,_) | Vregister(array,_,_,_) -> big_int_of_int (Array.length array)
  | VvectorR(array,_,_) -> big_int_of_int (Array.length array)
  | _ -> assert false

let arith_op op (l,r) = op l r
let add = arith_op add_big_int
let add_signed = arith_op add_big_int
let minus = arith_op sub_big_int
let multiply = arith_op mult_big_int
let modulo = arith_op mod_big_int
let quot = arith_op div_big_int
let power = arith_op power_big

let get_ord = function
  | Vvector(_,_,o) | Vregister(_,_,o,_) | VvectorR(_,_,o) -> o
  | _ -> assert false  

let arith_op_vec op sign size (l,r) =
  let ord = get_ord l in
  let (l',r') = to_num sign l, to_num sign r in
  let n = arith_op op (l',r') in
  to_vec ord (mult_big_int size (length l)) n

let add_vec = arith_op_vec add_big_int false unit_big_int
let add_vec_signed = arith_op_vec add_big_int true unit_big_int
let minus_vec = arith_op_vec sub_big_int false unit_big_int
let multiply_vec = arith_op_vec mult_big_int false two_big_int
let multiply_vec_signed = arith_op_vec mult_big_int true two_big_int

let arith_op_vec_range op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec op sign size (l, to_vec ord (length l) r)

let add_vec_range = arith_op_vec_range add_big_int false unit_big_int
let add_vec_range_signed = arith_op_vec_range add_big_int true unit_big_int
let minus_vec_range = arith_op_vec_range sub_big_int false unit_big_int
let mult_vec_range = arith_op_vec_range mult_big_int false two_big_int
let mult_vec_range_signed = arith_op_vec_range mult_big_int true two_big_int

let arith_op_range_vec op sign size (l,r) =
  let ord = get_ord r in
  arith_op_vec op sign size ((to_vec ord (length r) l), r)

let add_range_vec = arith_op_range_vec add_big_int false unit_big_int
let add_range_vec_signed = arith_op_range_vec add_big_int true unit_big_int
let minus_range_vec = arith_op_range_vec sub_big_int false unit_big_int
let mult_range_vec = arith_op_range_vec mult_big_int false two_big_int
let mult_range_vec_signed = arith_op_range_vec mult_big_int true two_big_int

let arith_op_range_vec_range op sign (l,r) = arith_op op (l, to_num sign r)

let add_range_vec_range = arith_op_range_vec_range add_big_int false
let add_range_vec_range_signed = arith_op_range_vec_range add_big_int true
let minus_range_vec_range = arith_op_range_vec_range sub_big_int false

let arith_op_vec_range_range op sign (l,r) = arith_op op (to_num sign l,r)

let add_vec_range_range = arith_op_vec_range_range add_big_int false
let add_vec_range_range_signed = arith_op_vec_range_range add_big_int true
let minus_vec_range_range = arith_op_vec_range_range sub_big_int false

let arith_op_vec_vec_range op sign (l,r) = 
  let (l',r') = (to_num sign l,to_num sign r) in
  arith_op op (l',r')

let add_vec_vec_range = arith_op_vec_vec_range add_big_int false
let add_vec_vec_range_signed = arith_op_vec_vec_range add_big_int true

let arith_op_vec_bit op sign size (l,r) =
  let ord = get_ord l in
  let l' = to_num sign l in
  let n = arith_op op (l', match r with | Vone -> unit_big_int | _ -> zero_big_int) in
  to_vec ord (mult_big_int (length l) size) n
    
let add_vec_bit = arith_op_vec_bit add_big_int false unit_big_int
let add_vec_bit_signed = arith_op_vec_bit add_big_int true unit_big_int
let minus_vec_bit = arith_op_vec_bit sub_big_int true unit_big_int

let rec arith_op_overflow_vec op sign size (l,r) =
  let ord = get_ord l in
  let len = length l in
  let act_size = mult_big_int len size in
  let (l_sign,r_sign) = (to_num sign l,to_num sign r) in
  let (l_unsign,r_unsign) = (to_num false l,to_num false r) in
  let n = arith_op op (l_sign,r_sign) in
  let n_unsign = arith_op op (l_unsign,r_unsign) in
  let correct_size_num = to_vec ord act_size n in
  let one_more_size_u = to_vec ord (succ_big_int act_size) n_unsign in
  let overflow = if (le_big_int n (get_max_representable_in sign (int_of_big_int len))) &&
                    (ge_big_int n (get_min_representable_in sign (int_of_big_int len)))
    then Vzero
    else Vone in
  let c_out = most_significant one_more_size_u in
  (correct_size_num,overflow,c_out)

let add_overflow_vec = arith_op_overflow_vec add_big_int false unit_big_int
let add_overflow_vec_signed = arith_op_overflow_vec add_big_int true unit_big_int
let minus_overflow_vec = arith_op_overflow_vec sub_big_int false unit_big_int
let minus_overflow_vec_signed = arith_op_overflow_vec sub_big_int true unit_big_int
let mult_overflow_vec = arith_op_overflow_vec mult_big_int false two_big_int
let mult_overflow_vec_signed = arith_op_overflow_vec mult_big_int true two_big_int
    
let rec arith_op_overflow_vec_bit op sign size (l,r_bit) =
  let ord = get_ord l in
  let act_size = mult_big_int (length l) size in
  let l' = to_num sign l in
  let l_u = to_num false l in
  let (n,nu,changed) = match r_bit with
    | Vone -> (arith_op op (l',unit_big_int), arith_op op (l_u,unit_big_int), true)
    | Vzero -> (l',l_u,false)
    | _ -> assert false
  in
  let correct_size_num = to_vec ord act_size n in
  let one_larger = to_vec ord (succ_big_int act_size) nu in
  let overflow =
    if changed 
    then if (le_big_int n (get_max_representable_in sign (int_of_big_int act_size))) &&
            (ge_big_int n (get_min_representable_in sign (int_of_big_int act_size)))
      then Vzero
      else Vone 
    else Vone in
        (correct_size_num,overflow,most_significant one_larger)

let add_overflow_vec_bit_signed = arith_op_overflow_vec_bit add_big_int true unit_big_int
let minus_overflow_vec_bit = arith_op_overflow_vec_bit sub_big_int false unit_big_int
let minus_overflow_vec_bit_signed = arith_op_overflow_vec_bit sub_big_int true unit_big_int
    
let shift_op_vec op (l,r) =
  match l with
  | Vvector(array,start,ord) | Vregister(array,start,ord,_) ->
    let len = Array.length array in
    let n = int_of_big_int r in
    (match op with
     | "<<" ->
       let right_vec = Vvector(Array.make n Vzero,0,true) in
       let left_vec = vector_subrange l n (if ord then len + start else start - len) in
       vector_append left_vec right_vec
     | ">>" ->
       let right_vec = vector_subrange l start n in
       let left_vec = Vvector(Array.make n Vzero,0,true) in
       vector_append left_vec right_vec 
     | "<<<" ->
       let left_vec = vector_subrange l n (if ord then len + start else start - len) in
       let right_vec = vector_subrange l start n in
       vector_append left_vec right_vec
     | _ -> assert false)
  | _ -> assert false

let bitwise_leftshift = shift_op_vec "<<"
let bitwise_rightshift = shift_op_vec ">>"
let bitwise_rotate = shift_op_vec "<<<"

let rec arith_op_no0 op (l,r) = 
  if eq_big_int r zero_big_int
  then None
  else Some (op l r)

let rec arith_op_vec_no0 op sign size (l,r) =
  let ord = get_ord l in
  let act_size = int_of_big_int (mult_big_int (length l) size) in
  let (l',r') = (to_num sign l,to_num sign r) in
  let n = arith_op op (l',r') in
  let representable,n' = 
    match n with 
    | Some n' ->  
      ((le_big_int n' (get_max_representable_in sign act_size)) &&
       (ge_big_int n' (get_min_representable_in sign act_size))), n'
    | _ -> false,zero_big_int in
  if representable 
  then to_vec ord (big_int_of_int act_size) n'
  else
    match l with
    | Vvector(_, start, _) | Vregister(_, start, _, _) ->
      Vvector((Array.make act_size Vundef), start, ord)
    | _ -> assert false

let arith_op_overflow_no0_vec op sign size (l,r) =
  let ord = get_ord l in
  let rep_size = mult_big_int (length r) size in
  let act_size = mult_big_int (length l) size in
  let (l',r') = ((to_num sign l),(to_num sign r)) in
  let (l_u,r_u) = (to_num false l,to_num false r) in
  let n = arith_op_no0 op (l',r') in
  let n_u = arith_op_no0 op (l_u,r_u) in
  let representable,n',n_u' = 
    match n, n_u with 
    | Some n',Some n_u' ->  
      ((le_big_int n' (get_max_representable_in sign (int_of_big_int rep_size))) &&
       (ge_big_int n' (get_min_representable_in sign (int_of_big_int rep_size))), n', n_u')
    | _ -> true,zero_big_int,zero_big_int in
  let (correct_size_num,one_more) = 
    if representable then
      (to_vec ord act_size n',to_vec ord (succ_big_int act_size) n_u')
    else match l with 
      | Vvector(_, start, _) | Vregister(_, start, _, _) ->
        Vvector((Array.make (int_of_big_int act_size) Vundef), start, ord),
        Vvector((Array.make  ((int_of_big_int act_size) + 1) Vundef), start, ord)
      | _ -> assert false in
  let overflow = if representable then Vzero else Vone in
  (correct_size_num,overflow,most_significant one_more)

let arith_op_vec_range_no0 op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec_no0 op sign size (l,(to_vec ord (length l) r))


