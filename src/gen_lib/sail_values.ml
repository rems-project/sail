open Big_int_Z
open Printf

(* only expected to be 0, 1, 2; 2 represents undef *)
type vbit = Vone | Vzero | Vundef
type number = Big_int_Z.big_int
type _bool = vbit
type _string = string
type _nat = number

type value =
  | Vvector of vbit array * int * bool
  | VvectorR of value array * int * bool
  | Vregister of vbit array ref * int * bool * (string * (int * int)) list
  | Vbit of vbit (*Mostly for Vundef in place of undefined register place holders*)

exception Sail_exit

let string_of_bit = function 
  | Vone   -> "1"
  | Vzero  -> "0"
  | Vundef -> "u"

let string_of_bit_array a = Array.fold_left (^) "" (Array.map string_of_bit a) 

let string_of_value = function
  | Vvector(bits, start, inc)  -> (string_of_int start) ^ (if inc then "inc" else "dec") ^ (string_of_bit_array bits)
  | VvectorR(values, start, inc) -> ""
  | Vregister(bits, start, inc, fields) -> "reg" ^ (string_of_int start) ^ (if inc then "inc" else "dec") ^ (string_of_bit_array !bits)
  | Vbit(b) -> string_of_bit b

let to_bool = function
  | Vzero -> false
  | Vone  -> true
  | Vundef -> assert false

let is_one i =
  if eq_big_int i unit_big_int
  then Vone
  else Vzero


let exit _ = raise Sail_exit


let is_one_int i =
  if i = 1 then Vone else Vzero

let get_barray  = function
  | Vvector(a,_,_) -> a
  | Vregister(a,_,_,_) -> !a
  | _ -> assert false

let get_varray = function
  | VvectorR(a,_,_) -> a
  | _ -> assert false

let get_ord = function
  | Vvector(_,_,o) | Vregister(_,_,o,_) | VvectorR(_,_,o) -> o
  | _ -> assert false  

let get_start = function
  | Vvector(_,s,o) | Vregister(_,s,o,_) | VvectorR(_,s,o) -> s
  | _ -> assert false  
  
let set_start i = function
  | Vvector(a,start,dir) -> Vvector(a,i,dir)
  | Vregister(bits,start,dir,regfields) -> Vregister(bits,i,dir,regfields)
  | VvectorR(a,start,dir) -> VvectorR(a,i,dir)
  | _ -> assert false  

let length_int = function
  | Vvector(array,_,_) -> Array.length array
  | Vregister(array,_,_,_) -> Array.length !array
  | VvectorR(array,_,_) -> Array.length array
  | _ -> assert false
  
let set_start_to_length v = set_start ((length_int v)-1) v (* XXX should take account of direction? *)

let length_big v = big_int_of_int (length_int v)
let length = length_big

let read_register = function
  | Vregister(a,start,inc,_) -> Vvector(!a,start,inc)
  | v -> v

let vector_access_int v n = 
  match v with
  | VvectorR(array,start,is_inc) ->
    if is_inc
    then (array.(n-start))
    else (array.(start-n))
  | _ -> assert false

let vector_access_big v n = vector_access_int v (int_of_big_int n)

let vector_access = vector_access_big

let bit_vector_access_int v n = match v with
  | Vvector(array,start,is_inc) ->
    if is_inc
    then array.(n-start)
    else array.(start-n)
  | Vregister(array,start,is_inc,_) ->
    if is_inc
    then !array.(n-start)
    else !array.(start-n)
  | _ -> assert false

let bit_vector_access_big v n = bit_vector_access_int v (int_of_big_int n)
let bit_vector_access = bit_vector_access_big

let vector_subrange_int v n m =
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
    Vvector(builder !array length offset Vzero,n,is_inc)
  | _ -> v

let vector_subrange_big v n m = vector_subrange_int v (int_of_big_int n) (int_of_big_int m)
let vector_subrange = vector_subrange_big

let get_register_field_vec reg field =
  match reg with
  | Vregister(_,_,_,fields) ->
    (match List.assoc field fields with
     | (i,j) ->
       if i = j
       then Vbit Vundef
       else vector_subrange_int reg i j)
  | _ -> Vbit Vundef

let get_register_field_bit reg field =
  match reg with
  | Vregister(_,_,_,fields) ->
    (match List.assoc field fields with
     | (i,j) ->
       if i = j
       then bit_vector_access_int reg i
       else Vundef)
  | _ -> Vundef

let set_register register value = match register,value with
  | Vregister(a,_,_,_), Vregister(new_v,_,_,_) ->
    a := !new_v
  | Vregister(a,_,_,_), Vvector(new_v,_,_) ->
    a := new_v
  | _ -> failwith "set_register of non-register"

let set_vector_subrange_vec_int v n m new_v =
  let walker array length offset new_values =
    begin
      for x = 0 to length-1
      do array.(x+offset) <- new_values.(x) 
      done;
    end
  in
  match v, new_v with
  | VvectorR(array,start,is_inc),VvectorR(new_v,_,_) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    walker array length offset new_v
  | _ -> ()

let set_vector_subrange_vec_big v n m new_v =
  set_vector_subrange_vec_int v (int_of_big_int n) (int_of_big_int m) new_v
let set_vector_subrange_vec = set_vector_subrange_vec_big (* or maybe _int *)

let set_vector_subrange_bit_int v n m new_v =
  let walker array length offset new_values =
    begin
      for x = 0 to length-1
      do array.(x+offset) <- new_values.(x) 
      done;
    end
  in
  match v,new_v with
  | Vvector(array,start,is_inc),Vvector(new_v,_,_) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    walker array length offset new_v
  | Vregister(array,start,is_inc,fields),Vvector(new_v,_,_) ->
    let (length,offset) = if is_inc then (m-n+1,n-start) else (n-m+1,start-n) in
    walker !array length offset new_v
  | _ -> ()

let set_vector_subrange_bit_big v n m new_v =
  set_vector_subrange_bit_int v (int_of_big_int n) (int_of_big_int m) new_v
let set_vector_subrange_bit = set_vector_subrange_bit_int

let set_register_bit_int reg n v = 
  match reg with
  | Vregister(array,start,inc,fields) ->
     (!array).(if inc then (n - start) else (start - n)) <- v
  | _ -> failwith "set_register_bit of non-register"
let set_register_bit_big reg n v = set_register_bit_int reg (int_of_big_int n) v
let set_register_bit = set_register_bit_big

let set_register_field_v reg field new_v =
  match reg with
  | Vregister(array,start,dir,fields) ->
    (match List.assoc field fields with
     | (i,j) ->
       if i = j
       then ()
       else set_vector_subrange_bit reg i j new_v)
  | _ -> ()

let set_register_field_bit reg field new_v =
  match reg with
  | Vregister(array,start,dir,fields) ->
    (match List.assoc field fields with
     | (i,j) ->
       if i = j
       then !array.(if dir then i - start else start - i) <- new_v
       else ())
  | _ -> ()

let set_two_reg r1 r2 vec =
  let size = length_int r1 in
  let dir = get_ord r1 in
  let start = get_start vec in
  let vsize = length_int vec in
  let r1_v = vector_subrange_int vec start ((if dir then size - start else start - size) - 1) in
  let r2_v = vector_subrange_int vec (if dir then size - start else start - size)
      (if dir then vsize - start else start - vsize) in
  begin set_register r1 r1_v; set_register r2 r2_v end
  

let make_indexed_v entries default start size dir =
  let default_value = match default with
    | None -> Vbit Vundef
    | Some v -> v in
  let array = Array.make size default_value in
  begin
    List.iter (fun (i,v) -> array.(if dir then start - i else i - start) <- v) entries;
    VvectorR(array, start, dir)
  end

let make_indexed_v_big entries default start size dir =
  make_indexed_v entries default (int_of_big_int start) (int_of_big_int size) dir

let make_indexed_bitv entries default start size dir =
  let default_value = match default with
    | None -> Vundef
    | Some v -> v in
  let array = Array.make size default_value in
  begin
    List.iter (fun (i,v) -> array.(if dir then start - i else i - start) <- v) entries;
    Vvector(array, start, dir)
  end

let make_indexed_bitv_big entries default start size dir =
  make_indexed_bitv entries default (int_of_big_int start) (int_of_big_int size) dir

let vector_concat l r =
  match l,r with
  | Vvector(arrayl,start,ord), Vvector(arrayr,_,_) ->
    Vvector(Array.append arrayl arrayr, start, ord)
  | Vvector(arrayl,start,ord), Vregister(arrayr,_,_,_) ->
    Vvector(Array.append arrayl !arrayr, start,ord)
  | Vregister(arrayl,start,ord,_), Vvector(arrayr,_,_) ->
    Vvector(Array.append !arrayl arrayr, start, ord)
  | Vregister(arrayl,start,ord,_), Vregister(arrayr,_,_,_) ->
    Vvector(Array.append !arrayl !arrayr,start,ord)
  | VvectorR(arrayl,start,ord),VvectorR(arrayr,_,_) ->
    VvectorR(Array.append arrayl arrayr, start,ord)
  | _ -> Vbit Vundef

let has_undef = function
  | Vvector(array,_,_) ->
    let rec foreach i =
      if i < Array.length array
      then
        if array.(i) = Vundef then true
        else foreach (i+1)
      else false in
    foreach 0
  | Vregister(array,_,_,_) ->
    let array = !array in
    let rec foreach i =
      if i < Array.length array
      then
        if array.(i) = Vundef then true
        else foreach (i+1)
      else false in
    foreach 0
  | _ -> false

let most_significant = function
  | Vvector(array,_,_) -> array.(0)
  | Vregister(array,_,_,_) -> !array.(0)
  | _ -> assert false

let bitwise_not_bit = function
  | Vone -> Vzero
  | Vzero -> Vone
  | _ -> Vundef

let bitwise_not = function
  | Vvector(array,s,d)-> Vvector( Array.map bitwise_not_bit array,s,d)
  | Vregister(array,s,d,_) -> Vvector( Array.map bitwise_not_bit !array,s,d)
  | _ -> assert false 

let bool_to_bit b = if b then Vone else Vzero

let bitwise_binop_bit op (l,r) =
  match l,r with
  | Vundef,_ | _,Vundef -> Vundef (*Do we want to do this or to respect | of One and & of Zero rules?*)
  | Vone,Vone -> bool_to_bit (op true true)
  | Vone,Vzero -> bool_to_bit (op true false)
  | Vzero,Vone -> bool_to_bit (op false true)
  | Vzero,Vzero -> bool_to_bit (op false false)

let bitwise_and_bit = bitwise_binop_bit (&&)
let bitwise_or_bit = bitwise_binop_bit (||)
let bitwise_xor_bit = bitwise_binop_bit (<>)

let bitwise_binop op (l,r) =
  let bop l arrayl arrayr =
    let array = Array.make l Vzero in
    begin
      for i = 0 to (l-1) do
        array.(i) <- bitwise_binop_bit op (arrayl.(i), arrayr.(i))
      done;
      array
    end in
  match l,r with
  | Vvector(arrayl, start, dir), Vvector(arrayr,_,_) ->
    Vvector(bop (Array.length arrayl) arrayl arrayr, start,dir)
  | Vvector(arrayl, start, dir), Vregister(arrayr,_,_,_) ->
    Vvector(bop (Array.length arrayl) arrayl !arrayr, start, dir)
  | Vregister(arrayl, start,dir,_), Vvector(arrayr,_,_) ->
    Vvector(bop (Array.length arrayr) !arrayl arrayr, start,dir)
  | Vregister(arrayl, start, dir, _), Vregister(arrayr,_,_,_) ->
    Vvector(bop (Array.length !arrayl) !arrayl !arrayr, start,dir)
  | _ -> Vbit Vundef

let bitwise_and = bitwise_binop (&&)
let bitwise_or = bitwise_binop (||)
let bitwise_xor = bitwise_binop (<>)

let rec power_int base raiseto =
  if raiseto = 0
  then 1
  else base * (power_int base (raiseto - 1))

let int_of_bit_array array = 
  let acc = ref 0 in
  let len = Array.length array in
  begin 
    for i = len - 1 downto 0 do
      match array.(len - i - 1) with
      | Vone -> acc := !acc + (power_int 2 i)
      | _ -> ()
    done;
    !acc
  end

let unsigned_int = function
  | (Vvector(array,_,_) as v) ->
    if has_undef v
    then assert false
    else int_of_bit_array array
  | (Vregister(array,_,_,_) as v)->
    let array = !array in
    if has_undef v
    then assert false
    else int_of_bit_array array
  | _ -> assert false

let big_int_of_bit_array array = 
  let acc = ref zero_big_int in
  let len = Array.length array in
  begin 
    for i = len - 1 downto 0 do
      match array.(len-i-1) with
      | Vone -> acc := add_big_int !acc (power_int_positive_int 2 i)
      | _ -> ()
    done;
    !acc
  end

let unsigned_big = function
  | (Vvector(array,_,_) as v) ->
    if has_undef v
    then assert false
    else
      big_int_of_bit_array array
  | (Vregister(array,_,_,_) as v)->
    let array = !array in
    if has_undef v
    then assert false
    else
      big_int_of_bit_array array
  | _ -> assert false

let unsigned = unsigned_big

let signed_int v =
  match most_significant v with
  | Vone -> -(1 + (unsigned_int (bitwise_not v)))
  | Vzero -> unsigned_int v
  | _ -> assert false

let signed_big v =
  match most_significant v with
  | Vone -> minus_big_int(add_int_big_int 1 (unsigned_big (bitwise_not v)))
  | Vzero -> unsigned_big v
  | _ -> assert false

let signed = signed_big

let to_num_int sign = if sign then signed_int else unsigned_int
let to_num_big sign = if sign then signed_big else unsigned_big
let to_num = to_num_big

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


let rec divide_by_2_big array i n =
  if i < 0 || eq_big_int n zero_big_int
  then array
  else let (quo,modu) = quomod_big_int n two_big_int in
    if eq_big_int modu unit_big_int
    then begin array.(i) <- Vone; divide_by_2_big array (i-1) quo end
    else divide_by_2_big array (i-1) quo

let rec divide_by_2_int array i n =
  if i < 0 || n = 0
  then array
  else let (quo,modu) = n/2, n mod 2 in
    if modu = 1
    then begin array.(i) <- Vone; divide_by_2_int array (i-1) quo end
    else divide_by_2_int array (i-1) quo

let rec add_one_bit array ci i =
  if i < 0
  then array
  else match array.(i),ci with
    | Vzero,false -> add_one_bit array false (i-1)
    | Vzero,true  -> array.(i) <- Vone; add_one_bit array false (i-1)
    | Vone, false -> array.(i) <- Vone; add_one_bit array false (i-1)
    | Vone, true  -> array.(i) <- Vzero; add_one_bit array true (i-1)
    | Vundef,_ -> assert false

let to_vec_int ord len n =
  let array = Array.make len Vzero in
  let start = if ord then 0 else len-1 in
  if n = 0
  then Vvector(array, start, ord)
  else if n >= 0 
  then Vvector(divide_by_2_int array (len -1) n, start, ord)
  else
    let abs_n = abs n in
    let abs_array = divide_by_2_int array (len-1) abs_n in
    let v_abs = bitwise_not (Vvector(abs_array,start,ord)) in
    match v_abs with
    | Vvector(array,start,ord) -> Vvector(add_one_bit array true (len-1),start,ord)
    | _ -> assert false

let to_vec_big ord len n =
  let len = int_of_big_int len in
  let array = Array.make len Vzero in
  let start = if ord then 0 else len-1 in
  if eq_big_int n zero_big_int
  then Vvector(array, start, ord)
  else if gt_big_int n zero_big_int
  then Vvector(divide_by_2_big array (len -1) n, start, ord)
  else
    let abs_n = abs_big_int n in
    let abs_array = divide_by_2_big array (len-1) abs_n in
    let v_abs = bitwise_not (Vvector(abs_array,start,ord)) in
    match v_abs with
    | Vvector(array,start,ord) -> Vvector(add_one_bit array true (len-1),start,ord)
    | _ -> assert false

let to_vec_inc_int (len,n) = to_vec_int true len n
let to_vec_dec_int (len,n) = to_vec_int false len n

let to_vec_inc_big (len,n) = to_vec_big true len n
let to_vec_dec_big (len,n) = to_vec_big false len n

let to_vec_inc = to_vec_inc_big
let to_vec_dec = to_vec_dec_big

let to_vec_undef_int ord len = 
  let array = Array.make len Vundef in
  let start = if ord then 0 else len-1 in
  Vvector(array, start, ord)

let to_vec_undef_big ord len = 
  let len = int_of_big_int len in
  let array = Array.make len Vundef in
  let start = if ord then 0 else len-1 in
  Vvector(array, start, ord)

let to_vec_inc_undef_int len = to_vec_undef_int true len
let to_vec_dec_undef_int len = to_vec_undef_int false len

let to_vec_inc_undef_big len = to_vec_undef_big true len
let to_vec_dec_undef_big len = to_vec_undef_big false len

let to_vec_inc_undef = to_vec_inc_undef_big
let to_vec_dec_undef = to_vec_dec_undef_big

let exts_int (len, vec) = 
  let barray = get_barray(vec) in
  let vlen = Array.length barray in
  let arr = 
    if (vlen < len) then
      (* copy most significant bit into new bits *)
      Array.append (Array.make (len - vlen) barray.(0)) barray
    else
      (* truncate to least significant bits *)
      Array.sub barray (vlen - len) len in
  let inc = get_ord vec in
  Vvector(arr, (if inc then 0 else (len - 1)), inc)

let extz_int (len, vec) = 
  let barray = get_barray(vec) in
  let vlen = Array.length barray in
  let arr = 
    if (vlen < len) then
      (* fill new bits with zero *)
      Array.append (Array.make (len - vlen) Vzero) barray
    else
      (* truncate to least significant bits *)
      Array.sub barray (vlen - len) len in
  let inc = get_ord vec in
  Vvector(arr, (if inc then 0 else (len - 1)), inc)

let exts_big (len,vec) = exts_int (int_of_big_int len, vec)
let extz_big (len,vec) = extz_int (int_of_big_int len, vec)

let exts = exts_big
let extz = extz_big

let arith_op op (l,r) = op l r
let add_big = arith_op add_big_int
let add_signed_big = arith_op add_big_int
let minus_big = arith_op sub_big_int
let multiply_big = arith_op mult_big_int
 (* this implements truncation towards zero like C and unlike ocaml (consider r < 0) *)
let quot_big (l, r) =
  let q = div_big_int (abs_big_int l) (abs_big_int r) in
  let lneg = lt_big_int l zero_big_int in
  let rneg = lt_big_int r zero_big_int in
  if (lneg <> rneg) then
    minus_big_int q
  else
    q
let modulo_big (l, r) = (* calculate mod given above quot *)
  let q = quot_big (l, r) in
  sub_big_int l (mult_big_int q r)

let power_big = arith_op power_big

let add_int = arith_op (+)
let add_signed_int = arith_op (+)
let minus_int = arith_op (-)
let multiply_int = arith_op ( * )
let modulo_int = arith_op (mod)
let quot_int (l, r) = 
  let q = (abs l) / (abs r) in
  let lneg = l < 0 in
  let rneg = r < 0 in
  if (lneg <> rneg) then
    -q
  else
    q
let modulo_int (l, r) = 
  let q = quot_int (l, r) in
  l - (r * q)

let power_int = arith_op power_int

let add        = add_big
let add_signed = add_signed_big
let minus      = minus_big
let multiply   = multiply_big
let modulo     = modulo_big
let quot       = quot_big
let power      = power_big

let arith_op_vec_big op sign size (l,r) =
  let ord = get_ord l in
  let (l',r') = to_num_big sign l, to_num_big sign r in
  let n = arith_op op (l',r') in
  to_vec_big ord (mult_big_int size (length_big l)) n

let add_vec_big = arith_op_vec_big add_big_int false unit_big_int
let add_vec_signed_big = arith_op_vec_big add_big_int true unit_big_int
let minus_vec_big = arith_op_vec_big sub_big_int false unit_big_int
let multiply_vec_big = arith_op_vec_big mult_big_int false two_big_int
let multiply_vec_signed_big = arith_op_vec_big mult_big_int true two_big_int

let arith_op_vec_int op sign size (l,r) =
  let ord = get_ord l in
  let (l',r') = to_num_int sign l, to_num_int sign r in
  let n = arith_op op (l',r') in
  to_vec_int ord (size * (length_int l)) n

let add_vec_int = arith_op_vec_int (+) false 1
let add_vec_signed_int = arith_op_vec_int (+) true 1
let minus_vec_int = arith_op_vec_int (-) false 1
let multiply_vec_int = arith_op_vec_int ( * ) false 2
let multiply_vec_signed_int = arith_op_vec_int ( * ) true 2

let add_vec             = add_vec_big            
let add_vec_signed      = add_vec_signed_big     
let minus_vec           = minus_vec_big          
let multiply_vec        = multiply_vec_big       
let multiply_vec_signed = multiply_vec_signed_big


let arith_op_vec_range_int op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec_int op sign size (l, to_vec_int ord (length_int l) r)

let add_vec_range_int = arith_op_vec_range_int (+) false 1
let add_vec_range_signed_int = arith_op_vec_range_int (+) true 1
let minus_vec_range_int = arith_op_vec_range_int (-) false 1
let mult_vec_range_int = arith_op_vec_range_int ( * ) false 2
let mult_vec_range_signed_int = arith_op_vec_range_int ( * ) true 2

let arith_op_vec_range_big op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec_big op sign size (l, to_vec_big ord (length_big l) r)

let add_vec_range_big         = arith_op_vec_range_big add_big_int false unit_big_int
let add_vec_range_signed_big  = arith_op_vec_range_big add_big_int true unit_big_int
let minus_vec_range_big       = arith_op_vec_range_big sub_big_int false unit_big_int
let mult_vec_range_big        = arith_op_vec_range_big mult_big_int false two_big_int
let mult_vec_range_signed_big = arith_op_vec_range_big mult_big_int true two_big_int

let add_vec_range         = add_vec_range_big        
let add_vec_range_signed  = add_vec_range_signed_big 
let minus_vec_range       = minus_vec_range_big      
let mult_vec_range        = mult_vec_range_big       
let mult_vec_range_signed = mult_vec_range_signed_big

let arith_op_range_vec_int op sign size (l,r) =
  let ord = get_ord r in
  arith_op_vec_int op sign size ((to_vec_int ord (length_int r) l), r)

let add_range_vec_int = arith_op_range_vec_int (+) false 1
let add_range_vec_signed_int = arith_op_range_vec_int (+) true 1
let minus_range_vec_int = arith_op_range_vec_int (-) false 1
let mult_range_vec_int = arith_op_range_vec_int ( * ) false 2
let mult_range_vec_signed_int = arith_op_range_vec_int ( * ) true 2

let arith_op_range_vec_big op sign size (l,r) =
  let ord = get_ord r in
  arith_op_vec_big op sign size ((to_vec_big ord (length_big r) l), r)

let add_range_vec_big         = arith_op_range_vec_big add_big_int false unit_big_int
let add_range_vec_signed_big  = arith_op_range_vec_big add_big_int true unit_big_int
let minus_range_vec_big       = arith_op_range_vec_big sub_big_int false unit_big_int
let mult_range_vec_big        = arith_op_range_vec_big mult_big_int false two_big_int
let mult_range_vec_signed_big = arith_op_range_vec_big mult_big_int true two_big_int

let add_range_vec         = add_range_vec_big         
let add_range_vec_signed  = add_range_vec_signed_big  
let minus_range_vec       = minus_range_vec_big       
let mult_range_vec        = mult_range_vec_big        
let mult_range_vec_signed = mult_range_vec_signed_big 


let arith_op_range_vec_range_int op sign (l,r) = arith_op op (l, to_num_int sign r)

let add_range_vec_range_int = arith_op_range_vec_range_int (+) false
let add_range_vec_range_signed_int = arith_op_range_vec_range_int (+) true
let minus_range_vec_range_int = arith_op_range_vec_range_int (-) false

let arith_op_range_vec_range_big op sign (l,r) = arith_op op (l, to_num_big sign r)

let add_range_vec_range_big = arith_op_range_vec_range_big add_big_int false
let add_range_vec_range_signed_big = arith_op_range_vec_range_big add_big_int true
let minus_range_vec_range_big = arith_op_range_vec_range_big sub_big_int false

let add_range_vec_range        = add_range_vec_range_big       
let add_range_vec_range_signed = add_range_vec_range_signed_big 
let minus_range_vec_range      = minus_range_vec_range_big     

let arith_op_vec_range_range_int op sign (l,r) = arith_op op (to_num_int sign l,r)

let add_vec_range_range_int = arith_op_vec_range_range_int (+) false
let add_vec_range_range_signed_int = arith_op_vec_range_range_int (+) true
let minus_vec_range_range_int = arith_op_vec_range_range_int (-) false

let arith_op_vec_range_range_big op sign (l,r) = arith_op op (to_num_big sign l,r)

let add_vec_range_range_big = arith_op_vec_range_range_big add_big_int false
let add_vec_range_range_signed_big = arith_op_vec_range_range_big add_big_int true
let minus_vec_range_range_big = arith_op_vec_range_range_big sub_big_int false

let add_vec_range_range        = add_vec_range_range_big        
let add_vec_range_range_signed = add_vec_range_range_signed_big 
let minus_vec_range_range      = minus_vec_range_range_big      


let arith_op_vec_vec_range_int op sign (l,r) = 
  let (l',r') = (to_num_int sign l,to_num_int sign r) in
  arith_op op (l',r')

let add_vec_vec_range_int        = arith_op_vec_vec_range_int (+) false
let add_vec_vec_range_signed_int = arith_op_vec_vec_range_int (+) true

let arith_op_vec_vec_range_big op sign (l,r) = 
  let (l',r') = (to_num_big sign l,to_num_big sign r) in
  arith_op op (l',r')

let add_vec_vec_range_big = arith_op_vec_vec_range_big add_big_int false
let add_vec_vec_range_signed_big = arith_op_vec_vec_range_big add_big_int true

let add_vec_vec_range        = add_vec_vec_range_big       
let add_vec_vec_range_signed = add_vec_vec_range_signed_big

let arith_op_vec_bit_int op sign (l,r) =
  let ord = get_ord l in
  let l' = to_num_int sign l in
  let n = arith_op op (l', match r with | Vone -> 1 | _ -> 0) in
  to_vec_int ord (length_int l) n
    
let add_vec_bit_int = arith_op_vec_bit_int (+) false
let add_vec_bit_signed_int = arith_op_vec_bit_int (+) true 
let minus_vec_bit_int = arith_op_vec_bit_int (-) true

let arith_op_vec_bit_big op sign (l,r) =
  let ord = get_ord l in
  let l' = to_num_big sign l in
  let n = arith_op op (l', match r with | Vone -> unit_big_int | _ -> zero_big_int) in
  to_vec_big ord (length_big l) n
    
let add_vec_bit_big = arith_op_vec_bit_big add_big_int false 
let add_vec_bit_signed_big = arith_op_vec_bit_big add_big_int true
let minus_vec_bit_big = arith_op_vec_bit_big sub_big_int true

let add_vec_bit        = add_vec_bit_big       
let add_vec_bit_signed = add_vec_bit_signed_big
let minus_vec_bit      = minus_vec_bit_big     


let rec arith_op_overflow_vec_int op sign size (l,r) =
  let ord = get_ord l in
  let len = length_int l in
  let act_size = len * size in
  let (l_sign,r_sign) = (to_num_int sign l,to_num_int sign r) in
  let (l_unsign,r_unsign) = (to_num_int false l,to_num_int false r) in
  let n = arith_op op (l_sign,r_sign) in
  let n_unsign = arith_op op (l_unsign,r_unsign) in
  let correct_size_num = to_vec_int ord act_size n in
  let one_more_size_u = to_vec_int ord (act_size +1) n_unsign in
  let overflow = if (n <= (int_of_big_int (get_max_representable_in sign len))) &&
                    (n >= (int_of_big_int (get_min_representable_in sign len)))
    then Vzero
    else Vone in
  let c_out = most_significant one_more_size_u in
  (correct_size_num,overflow,c_out)

let add_overflow_vec_int = arith_op_overflow_vec_int (+) false 1
let add_overflow_vec_signed_int = arith_op_overflow_vec_int (+) true 1
let minus_overflow_vec_int = arith_op_overflow_vec_int (-) false 1
let minus_overflow_vec_signed_int = arith_op_overflow_vec_int (-) true 1
let mult_overflow_vec_int = arith_op_overflow_vec_int ( * ) false 2
let mult_overflow_vec_signed_int = arith_op_overflow_vec_int ( * ) true 2

let rec arith_op_overflow_vec_big op sign size (l,r) =
  let ord = get_ord l in
  let len = length_big l in
  let act_size = mult_big_int len size in
  let (l_sign,r_sign) = (to_num_big sign l,to_num_big sign r) in
  let (l_unsign,r_unsign) = (to_num_big false l,to_num_big false r) in
  let n = arith_op op (l_sign,r_sign) in
  let n_unsign = arith_op op (l_unsign,r_unsign) in
  let correct_size_num = to_vec_big ord act_size n in
  let one_more_size_u = to_vec_big ord (succ_big_int act_size) n_unsign in
  let overflow = if (le_big_int n (get_max_representable_in sign (int_of_big_int len))) &&
                    (ge_big_int n (get_min_representable_in sign (int_of_big_int len)))
    then Vzero
    else Vone in
  let c_out = most_significant one_more_size_u in
  (correct_size_num,overflow,c_out)

let add_overflow_vec_big = arith_op_overflow_vec_big add_big_int false unit_big_int
let add_overflow_vec_signed_big = arith_op_overflow_vec_big add_big_int true unit_big_int
let minus_overflow_vec_big = arith_op_overflow_vec_big sub_big_int false unit_big_int
let minus_overflow_vec_signed_big = arith_op_overflow_vec_big sub_big_int true unit_big_int
let mult_overflow_vec_big = arith_op_overflow_vec_big mult_big_int false two_big_int
let mult_overflow_vec_signed_big = arith_op_overflow_vec_big mult_big_int true two_big_int

let add_overflow_vec          = add_overflow_vec_big          
let add_overflow_vec_signed   = add_overflow_vec_signed_big   
let minus_overflow_vec        = minus_overflow_vec_big        
let minus_overflow_vec_signed = minus_overflow_vec_signed_big 
let mult_overflow_vec         = mult_overflow_vec_big         
let mult_overflow_vec_signed  = mult_overflow_vec_signed_big  

let rec arith_op_overflow_vec_bit_int op sign (l,r_bit) =
  let ord = get_ord l in
  let act_size = length_int l in
  let l' = to_num_int sign l in
  let l_u = to_num_int false l in
  let (n,nu,changed) = match r_bit with
    | Vone -> (arith_op op (l',1), arith_op op (l_u,1), true)
    | Vzero -> (l',l_u,false)
    | _ -> assert false
  in
  let correct_size_num = to_vec_int ord act_size n in
  let one_larger = to_vec_int ord (1+ act_size) nu in
  let overflow =
    if changed 
    then if (n <= (int_of_big_int (get_max_representable_in sign act_size))) &&
            (n >= (int_of_big_int (get_min_representable_in sign act_size)))
      then Vzero
      else Vone 
    else Vone in
        (correct_size_num,overflow,most_significant one_larger)

let add_overflow_vec_bit_signed_int = arith_op_overflow_vec_bit_int (+) true 
let minus_overflow_vec_bit_int = arith_op_overflow_vec_bit_int (-) false 
let minus_overflow_vec_bit_signed_int = arith_op_overflow_vec_bit_int (-) true

let rec arith_op_overflow_vec_bit_big op sign (l,r_bit) =
  let ord = get_ord l in
  let act_size = length_big l in
  let l' = to_num_big sign l in
  let l_u = to_num_big false l in
  let (n,nu,changed) = match r_bit with
    | Vone -> (arith_op op (l',unit_big_int), arith_op op (l_u,unit_big_int), true)
    | Vzero -> (l',l_u,false)
    | _ -> assert false
  in
  let correct_size_num = to_vec_big ord act_size n in
  let one_larger = to_vec_big ord (succ_big_int act_size) nu in
  let overflow =
    if changed 
    then if (le_big_int n (get_max_representable_in sign (int_of_big_int act_size))) &&
            (ge_big_int n (get_min_representable_in sign (int_of_big_int act_size)))
      then Vzero
      else Vone 
    else Vone in
        (correct_size_num,overflow,most_significant one_larger)

let add_overflow_vec_bit_signed_big = arith_op_overflow_vec_bit_big add_big_int true
let minus_overflow_vec_bit_big = arith_op_overflow_vec_bit_big sub_big_int false 
let minus_overflow_vec_bit_signed_big = arith_op_overflow_vec_bit_big sub_big_int true

let add_overflow_vec_bit_signed   = add_overflow_vec_bit_signed_big   
let minus_overflow_vec_bit        = minus_overflow_vec_bit_big        
let minus_overflow_vec_bit_signed = minus_overflow_vec_bit_signed_big 

let shift_op_vec_int op (l,r) =
  match l with
  | Vvector(_,start,ord) | Vregister(_,start,ord,_) ->
    let array = match l with | Vvector(array,_,_) -> array | Vregister(array,_,_,_) -> !array | _ -> assert false in
    let len = Array.length array in
    (match op with
     | "<<" ->
       let left = Array.sub array r (len - r) in
       let right = Array.make r Vzero in
       let result = Array.append left right in
       Vvector(result, start, ord)
     | ">>" ->
       let left = Array.make r Vzero in
       let right = Array.sub array 0 (len - r) in
       let result = Array.append left right in
       Vvector(result, start, ord)
     | "<<<" ->
       let left = Array.sub array r (len - r) in
       let right = Array.sub array 0 r in
       let result = Array.append left right in
       Vvector(result, start, ord)
     | _ -> assert false)
  | _ -> assert false

let shift_op_vec_big op (l,r) = shift_op_vec_int op (l, int_of_big_int r)
let bitwise_leftshift_big = shift_op_vec_big "<<"
let bitwise_rightshift_big = shift_op_vec_big ">>"
let bitwise_rotate_big = shift_op_vec_big "<<<"

let bitwise_leftshift = bitwise_leftshift_big
let bitwise_rightshift = bitwise_rightshift_big
let bitwise_rotate = bitwise_rotate_big

let rec arith_op_no0_big op (l,r) = 
  if eq_big_int r zero_big_int
  then None
  else Some (op l r)

let modulo_no0_big = arith_op_no0_big mod_big_int
let quot_no0_big = arith_op_no0_big div_big_int

let rec arith_op_no0_int op (l,r) = 
  if r = 0
  then None
  else Some (op l r)

let rec arith_op_vec_no0_int op sign size (l,r) =
  let ord = get_ord l in
  let act_size = ((length_int l) * size) in
  let (l',r') = (to_num_int sign l,to_num_int sign r) in
  let n = arith_op_no0_int op (l',r') in
  let representable,n' = 
    match n with 
    | Some n' ->  
      ((n' <= (int_of_big_int (get_max_representable_in sign act_size))) &&
       (n' >= (int_of_big_int (get_min_representable_in sign act_size)))), n'
    | _ -> false,0 in
  if representable 
  then to_vec_int ord act_size n'
  else
    match l with
    | Vvector(_, start, _) | Vregister(_, start, _, _) ->
      Vvector((Array.make act_size Vundef), start, ord)
    | _ -> assert false

let mod_vec_int = arith_op_vec_no0_int (mod) false 1
let quot_vec_int = arith_op_vec_no0_int (/) false 1
let quot_vec_signed_int = arith_op_vec_no0_int (/) true 1

let rec arith_op_vec_no0_big op sign size (l,r) =
  let ord = get_ord l in
  let act_size = int_of_big_int (mult_int_big_int (length_int l) size) in
  let (l',r') = (to_num_big sign l,to_num_big sign r) in
  let n = arith_op_no0_big op (l',r') in
  let representable,n' = 
    match n with 
    | Some n' ->  
      ((le_big_int n' (get_max_representable_in sign act_size)) &&
       (ge_big_int n' (get_min_representable_in sign act_size))), n'
    | _ -> false,zero_big_int in
  if representable 
  then to_vec_big ord (big_int_of_int act_size) n'
  else
    match l with
    | Vvector(_, start, _) | Vregister(_, start, _, _) ->
      Vvector((Array.make act_size Vundef), start, ord)
    | _ -> assert false

let mod_vec_big = arith_op_vec_no0_big mod_big_int false unit_big_int
let quot_vec_big = arith_op_vec_no0_big div_big_int false unit_big_int
let quot_vec_signed_big = arith_op_vec_no0_big div_big_int true unit_big_int

let mod_vec         = mod_vec_big         
let quot_vec        = quot_vec_big        
let quot_vec_signed = quot_vec_signed_big 

let arith_op_overflow_no0_vec_int op sign size (l,r) =
  let ord = get_ord l in
  let rep_size = (length_int r) * size in
  let act_size = (length_int l) * size in
  let (l',r') = ((to_num_int sign l),(to_num_int sign r)) in
  let (l_u,r_u) = (to_num_int false l,to_num_int false r) in
  let n = arith_op_no0_int op (l',r') in
  let n_u = arith_op_no0_int op (l_u,r_u) in
  let representable,n',n_u' = 
    match n, n_u with 
    | Some n',Some n_u' ->  
      ((n' <= (int_of_big_int (get_max_representable_in sign rep_size))) &&
       (n' >= (int_of_big_int (get_min_representable_in sign rep_size))), n', n_u')
    | _ -> true,0,0 in
  let (correct_size_num,one_more) = 
    if representable then
      (to_vec_int ord act_size n',to_vec_int ord (1+act_size) n_u')
    else match l with 
      | Vvector(_, start, _) | Vregister(_, start, _, _) ->
        Vvector((Array.make act_size Vundef), start, ord),
        Vvector((Array.make  (act_size + 1) Vundef), start, ord)
      | _ -> assert false in
  let overflow = if representable then Vzero else Vone in
  (correct_size_num,overflow,most_significant one_more)

let quot_overflow_vec_int = arith_op_overflow_no0_vec_int (/) false 1
let quot_overflow_vec_signed_int = arith_op_overflow_no0_vec_int (/) true 1

let arith_op_overflow_no0_vec_big op sign size (l,r) =
  let ord = get_ord l in
  let rep_size = mult_big_int (length_big r) size in
  let act_size = mult_big_int (length_big l) size in
  let (l',r') = ((to_num_big sign l),(to_num_big sign r)) in
  let (l_u,r_u) = (to_num_big false l,to_num_big false r) in
  let n = arith_op_no0_big op (l',r') in
  let n_u = arith_op_no0_big op (l_u,r_u) in
  let representable,n',n_u' = 
    match n, n_u with 
    | Some n',Some n_u' ->  
      ((le_big_int n' (get_max_representable_in sign (int_of_big_int rep_size))) &&
       (ge_big_int n' (get_min_representable_in sign (int_of_big_int rep_size))), n', n_u')
    | _ -> true,zero_big_int,zero_big_int in
  let (correct_size_num,one_more) = 
    if representable then
      (to_vec_big ord act_size n',to_vec_big ord (succ_big_int act_size) n_u')
    else match l with 
      | Vvector(_, start, _) | Vregister(_, start, _, _) ->
        Vvector((Array.make (int_of_big_int act_size) Vundef), start, ord),
        Vvector((Array.make  ((int_of_big_int act_size) + 1) Vundef), start, ord)
      | _ -> assert false in
  let overflow = if representable then Vzero else Vone in
  (correct_size_num,overflow,most_significant one_more)

let quot_overflow_vec_big = arith_op_overflow_no0_vec_big div_big_int false unit_big_int 
let quot_overflow_vec_signed_big = arith_op_overflow_no0_vec_big div_big_int true unit_big_int 

let quot_overflow_vec        = quot_overflow_vec_big        
let quot_overflow_vec_signed = quot_overflow_vec_signed_big 


let arith_op_vec_range_no0_int op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec_no0_int op sign size (l,(to_vec_int ord (length_int l) r))

let mod_vec_range_int = arith_op_vec_range_no0_int (mod) false 1

let arith_op_vec_range_no0_big op sign size (l,r) =
  let ord = get_ord l in
  arith_op_vec_no0_big op sign size (l,(to_vec_big ord (length_big l) r))

let mod_vec_range_big = arith_op_vec_range_no0_big mod_big_int false unit_big_int

let mod_vec_range = mod_vec_range_big

(* XXX Need to have a default top level direction reference I think*)
let duplicate_int (bit,length) =
  Vvector((Array.make length bit), (length-1), false)

let duplicate_big (bit,length) =
  duplicate_int (bit, int_of_big_int length)

let duplicate = duplicate_big

let compare_op op (l,r) =
  if (op l r)
  then Vone
  else Vzero

let lt_big = compare_op lt_big_int
let gt_big = compare_op gt_big_int
let lteq_big = compare_op le_big_int
let gteq_big = compare_op ge_big_int
let lt_int : (int* int) -> vbit = compare_op (<)
let gt_int : (int * int) -> vbit = compare_op (>)
let lteq_int : (int * int) -> vbit = compare_op (<=)
let gteq_int : (int*int) -> vbit = compare_op (>=)

let lt = lt_big
let gt = gt_big
let lteq = lteq_big
let gteq = gteq_big

let compare_op_vec_int op sign (l,r) = 
  let (l',r') = (to_num_int sign l, to_num_int sign r) in
  compare_op op (l',r')

let lt_vec_int = compare_op_vec_int (<) true
let gt_vec_int = compare_op_vec_int (>) true
let lteq_vec_int = compare_op_vec_int (<=) true
let gteq_vec_int = compare_op_vec_int (>=) true
let lt_vec_signed_int = compare_op_vec_int (<) true
let gt_vec_signed_int = compare_op_vec_int (>) true
let lteq_vec_signed_int = compare_op_vec_int (<=) true
let gteq_vec_signed_int = compare_op_vec_int (>=) true
let lt_vec_unsigned_int = compare_op_vec_int (<) false
let gt_vec_unsigned_int = compare_op_vec_int (>) false
let lteq_vec_unsigned_int = compare_op_vec_int (<=) false
let gteq_vec_unsigned_int = compare_op_vec_int (>=) false

let compare_op_vec_big op sign (l,r) = 
  let (l',r') = (to_num_big sign l, to_num_big sign r) in
  compare_op op (l',r')

let lt_vec_big = compare_op_vec_big lt_big_int true
let gt_vec_big = compare_op_vec_big gt_big_int true
let lteq_vec_big = compare_op_vec_big le_big_int true
let gteq_vec_big = compare_op_vec_big ge_big_int true
let lt_vec_signed_big = compare_op_vec_big lt_big_int true
let gt_vec_signed_big = compare_op_vec_big gt_big_int true
let lteq_vec_signed_big = compare_op_vec_big le_big_int true
let gteq_vec_signed_big = compare_op_vec_big ge_big_int true
let lt_vec_unsigned_big = compare_op_vec_big lt_big_int false
let gt_vec_unsigned_big = compare_op_vec_big gt_big_int false
let lteq_vec_unsigned_big = compare_op_vec_big le_big_int false
let gteq_vec_unsigned_big = compare_op_vec_big ge_big_int false

let lt_vec            = lt_vec_big            
let gt_vec            = gt_vec_big            
let lteq_vec          = lteq_vec_big          
let gteq_vec          = gteq_vec_big          
let lt_vec_signed     = lt_vec_signed_big     
let gt_vec_signed     = gt_vec_signed_big     
let lteq_vec_signed   = lteq_vec_signed_big   
let gteq_vec_signed   = gteq_vec_signed_big   
let lt_vec_unsigned   = lt_vec_unsigned_big   
let gt_vec_unsigned   = gt_vec_unsigned_big   
let lteq_vec_unsigned = lteq_vec_unsigned_big 
let gteq_vec_unsigned = gteq_vec_unsigned_big 

let compare_op_vec_range_int op sign (l,r) = 
  compare_op op ((to_num_int sign l),r)

let lt_vec_range_int = compare_op_vec_range_int (<) true
let gt_vec_range_int = compare_op_vec_range_int (>) true
let lteq_vec_range_int = compare_op_vec_range_int (<=) true
let gteq_vec_range_int = compare_op_vec_range_int (>=) true

let compare_op_vec_range_big op sign (l,r) = 
  compare_op op ((to_num_big sign l),r)

let lt_vec_range_big = compare_op_vec_range_big lt_big_int true
let gt_vec_range_big = compare_op_vec_range_big gt_big_int true
let lteq_vec_range_big = compare_op_vec_range_big le_big_int true
let gteq_vec_range_big = compare_op_vec_range_big ge_big_int true

let lt_vec_range   = lt_vec_range_big   
let gt_vec_range   = gt_vec_range_big   
let lteq_vec_range = lteq_vec_range_big 
let gteq_vec_range = gteq_vec_range_big 

let compare_op_range_vec_int op sign (l,r) =
  compare_op op (l, (to_num_int sign r))

let lt_range_vec_int = compare_op_range_vec_int (<) true
let gt_range_vec_int = compare_op_range_vec_int (>) true
let lteq_range_vec_int = compare_op_range_vec_int (<=) true
let gteq_range_vec_int = compare_op_range_vec_int (>=) true

let compare_op_range_vec_big op sign (l,r) =
  compare_op op (l, (to_num_big sign r))

let lt_range_vec_big = compare_op_range_vec_big lt_big_int true
let gt_range_vec_big = compare_op_range_vec_big gt_big_int true
let lteq_range_vec_big = compare_op_range_vec_big le_big_int true
let gteq_range_vec_big = compare_op_range_vec_big ge_big_int true

let lt_range_vec   = lt_range_vec_big   
let gt_range_vec   = gt_range_vec_big   
let lteq_range_vec = lteq_range_vec_big 
let gteq_range_vec = gteq_range_vec_big 

let eq (l,r) = if l = r then Vone else Vzero
let eq_vec_vec (l,r) = eq (to_num_big true l, to_num_big true r)
let eq_vec (l,r) = eq_vec_vec(l,r)
let eq_vec_range (l,r) = eq (to_num_big false l,r)
let eq_range_vec (l,r) = eq (l, to_num_big false r)
let eq_range = eq
let eq_bit = bitwise_binop_bit (=)

let neq (l,r) = bitwise_not_bit (eq (l,r))
let neq_vec (l,r) = bitwise_not_bit (eq_vec_vec(l,r))
let neq_bit (l,r) = bitwise_not_bit (eq_bit(l,r))

let mask (n,v) = 
  let n' = int_of_big_int n in
  match v with
  | Vvector (bits,start,dir) ->
     let current_size = Array.length bits in 
     let to_drop = (current_size - n') in
     let bits' = Array.sub bits to_drop n' in
     Vvector (bits',(if dir then 0 else n'-1), dir)
  | VvectorR (bits,start,dir) ->
     let current_size = Array.length bits in 
     let to_drop = (current_size - n') in
     let bits' = Array.sub bits to_drop n' in
     VvectorR (bits',(if dir then 0 else n'-1), dir)
  | Vregister _ -> failwith "mask not implemented for Vregister"
  | Vbit _ -> failwith "mask called for bit"

let slice_raw (v, i, j) = 
  let i' = int_of_big_int i in
  let j' = int_of_big_int j in
  match v with
  | Vvector (bs, start, is_inc) ->
     let bits = Array.sub bs i' (j'-i'+1) in
     let len = Array.length bits in
     Vvector (bits, (if is_inc then 0 else len - 1), is_inc)
  | _ -> failwith "slice_raw only implemented for VVector"
let _slice_raw = slice_raw
