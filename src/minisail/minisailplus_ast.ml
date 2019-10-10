module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Z.t -> bool -> int32
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Z.to_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Bits_Integer : sig
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
  val test_bit : Z.t -> Z.t -> bool
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

let test_bit x n =  Z.testbit x (Z.to_int n);;

end;; (*struct Bits_Integer*)

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Product_Type : sig
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val equal_bool : bool -> bool -> bool
end = struct

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

end;; (*struct Product_Type*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

end;; (*struct Orderings*)

module Arith : sig
  val equal_integer : Z.t HOL.equal
  type num = One | Bit0 of num | Bit1 of num
  val one_integera : Z.t
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_integer : Z.t one
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val zero_integer : Z.t zero
  val ord_integer : Z.t Orderings.ord
  type 'a zero_neq_one =
    {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero}
  val zero_neq_one_integer : Z.t zero_neq_one
  type int = Int_of_integer of Z.t
  type nat = Nat of Z.t
  val integer_of_int : int -> Z.t
  val nat : int -> nat
  val integer_of_nat : nat -> Z.t
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val suc : nat -> nat
  val one_int : int
  val less_int : int -> int -> bool
  val less_nat : nat -> nat -> bool
  val int_of_nat : nat -> int
  val plus_int : int -> int -> int
  val zero_int : int
  val zero_nat : nat
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val nat_of_integer : Z.t -> nat
  val bit_cut_integer : Z.t -> Z.t * bool
  val minus_int : int -> int -> int
  val equal_nat : nat -> nat -> bool
  val minus_nat : nat -> nat -> nat
  val less_eq_nat : nat -> nat -> bool
  val uminus_int : int -> int
  val of_bool : 'a zero_neq_one -> bool -> 'a
  val divide_integer : Z.t -> Z.t -> Z.t
  val divide_nat : nat -> nat -> nat
  val modulo_integer : Z.t -> Z.t -> Z.t
  val modulo_nat : nat -> nat -> nat
end = struct

let equal_integer = ({HOL.equal = Z.equal} : Z.t HOL.equal);;

type num = One | Bit0 of num | Bit1 of num;;

let one_integera : Z.t = (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_integer = ({one = one_integera} : Z.t one);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_integer = ({zero = Z.zero} : Z.t zero);;

let ord_integer =
  ({Orderings.less_eq = Z.leq; Orderings.less = Z.lt} : Z.t Orderings.ord);;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Z.t zero_neq_one);;

type int = Int_of_integer of Z.t;;

type nat = Nat of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec nat k = Nat (Orderings.max ord_integer Z.zero (integer_of_int k));;

let rec integer_of_nat (Nat x) = x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let one_int : int = Int_of_integer (Z.of_int 1);;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec plus_int
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

let zero_int : int = Int_of_integer Z.zero;;

let zero_nat : nat = Nat Z.zero;;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else Product_Type.apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec nat_of_integer k = Nat (Orderings.max ord_integer Z.zero k);;

let rec bit_cut_integer
  k = (if Z.equal k Z.zero then (Z.zero, false)
        else (let (r, s) =
                (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                  k (Z.of_int 2)
                in
               ((if Z.lt Z.zero k then r else Z.sub (Z.neg r) s),
                 Z.equal s (Z.of_int 1))));;

let rec minus_int
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec equal_nat m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let rec minus_nat
  m n = Nat (Orderings.max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec uminus_int k = Int_of_integer (Z.neg (integer_of_int k));;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec divide_integer k l = Product_Type.fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec modulo_integer k l = Product_Type.snd (divmod_integer k l);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

end;; (*struct Arith*)

module Fun : sig
  val id : 'a -> 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module Lista : sig
  val nth : 'a list -> Arith.nat -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val upto_aux : Arith.int -> Arith.int -> Arith.int list -> Arith.int list
  val upto : Arith.int -> Arith.int -> Arith.int list
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val hd : 'a list -> 'a
  val remdups : 'a HOL.equal -> 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val enumerate : Arith.nat -> 'a list -> (Arith.nat * 'a) list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val list_update : 'a list -> Arith.nat -> 'a -> 'a list
  val list_all : ('a -> bool) -> 'a list -> bool
  val size_list : 'a list -> Arith.nat
  val equal_list : 'a HOL.equal -> 'a list -> 'a list -> bool
end = struct

let rec nth
  (x :: xs) n =
    (if Arith.equal_nat n Arith.zero_nat then x
      else nth xs (Arith.minus_nat n Arith.one_nat));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec upt
  i j = (if Arith.less_nat i j then i :: upt (Arith.suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec upto_aux
  i j js =
    (if Arith.less_int j i then js
      else upto_aux i (Arith.minus_int j Arith.one_int) (j :: js));;

let rec upto i j = upto_aux i j [];;

let rec foldr f x1 = match f, x1 with f, [] -> Fun.id
                | f, x :: xs -> Fun.comp (f x) (foldr f xs);;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> HOL.eq _A x y || member _A xs y;;

let rec hd (x21 :: x22) = x21;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if member _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec enumerate
  n x1 = match n, x1 with n, x :: xs -> (n, x) :: enumerate (Arith.suc n) xs
    | n, [] -> [];;

let rec gen_length
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.suc n) xs
    | n, [] -> n;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if Arith.equal_nat i Arith.zero_nat then y :: xs
          else x :: list_update xs (Arith.minus_nat i Arith.one_nat) y);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec size_list x = gen_length Arith.zero_nat x;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

end;; (*struct Lista*)

module Z3 : sig
  type z3_expr = Z3E_num of Z.t | Z3E_var of string | Z3E_true | Z3E_false |
    Z3E_unit | Z3E_bitone | Z3E_bitzero | Z3E_len of z3_expr |
    Z3E_leq of z3_expr * z3_expr | Z3E_geq of z3_expr * z3_expr |
    Z3E_plus of z3_expr * z3_expr | Z3E_times of z3_expr * z3_expr |
    Z3E_div of z3_expr * z3_expr | Z3E_mod of z3_expr * z3_expr |
    Z3E_minus of z3_expr * z3_expr | Z3E_eq of z3_expr * z3_expr |
    Z3E_not of z3_expr | Z3E_and of z3_expr * z3_expr |
    Z3E_or of z3_expr * z3_expr | Z3E_neq of z3_expr * z3_expr |
    Z3E_bitvec of string | Z3E_constr of string * z3_expr list |
    Z3E_concat of z3_expr list | Z3E_proj of string * z3_expr |
    Z3E_string of string
  val equal_z3_expr : z3_expr HOL.equal
  val equal_z3_expra : z3_expr -> z3_expr -> bool
  type z3_bool_expr = Z3BE_true | Z3BE_false | Z3BE_not of z3_bool_expr |
    Z3BE_and of z3_bool_expr list | Z3BE_or of z3_bool_expr list |
    Z3BE_eq of z3_expr * z3_expr | Z3BE_leq of z3_expr * z3_expr |
    Z3BE_implies of z3_bool_expr * z3_bool_expr
  val equal_z3_bool_expr : z3_bool_expr HOL.equal
  val equal_z3_bool_expra : z3_bool_expr -> z3_bool_expr -> bool
  type z3_type = Z3T_int | Z3T_bool | Z3T_unit | Z3T_array of z3_type * z3_type
    | Z3T_dt of string * z3_type list | Z3T_sort of string | Z3T_string
  type z3_type_var = Z3TV_tv_type of z3_type | Z3TV_tv_var of Z.t
  type z3_constr = Z3C_ty_constr of string * (string * z3_type_var) list
  type z3_decl = Z3D_decl_fun | Z3D_decl_const of string * z3_type |
    Z3D_decl_datatype of string * z3_type_var list * z3_constr list
end = struct

type z3_expr = Z3E_num of Z.t | Z3E_var of string | Z3E_true | Z3E_false |
  Z3E_unit | Z3E_bitone | Z3E_bitzero | Z3E_len of z3_expr |
  Z3E_leq of z3_expr * z3_expr | Z3E_geq of z3_expr * z3_expr |
  Z3E_plus of z3_expr * z3_expr | Z3E_times of z3_expr * z3_expr |
  Z3E_div of z3_expr * z3_expr | Z3E_mod of z3_expr * z3_expr |
  Z3E_minus of z3_expr * z3_expr | Z3E_eq of z3_expr * z3_expr |
  Z3E_not of z3_expr | Z3E_and of z3_expr * z3_expr |
  Z3E_or of z3_expr * z3_expr | Z3E_neq of z3_expr * z3_expr |
  Z3E_bitvec of string | Z3E_constr of string * z3_expr list |
  Z3E_concat of z3_expr list | Z3E_proj of string * z3_expr |
  Z3E_string of string;;

let rec equal_z3_expr () = ({HOL.equal = equal_z3_expra} : z3_expr HOL.equal)
and equal_z3_expra
  x0 x1 = match x0, x1 with Z3E_proj (x241, x242), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_proj (x241, x242) -> false
    | Z3E_concat x23, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_concat x23 -> false
    | Z3E_constr (x221, x222), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_constr (x221, x222) -> false
    | Z3E_bitvec x21, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_bitvec x21 -> false
    | Z3E_neq (x201, x202), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_neq (x201, x202) -> false
    | Z3E_or (x191, x192), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_or (x191, x192) -> false
    | Z3E_and (x181, x182), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_and (x181, x182) -> false
    | Z3E_not x17, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_not x17 -> false
    | Z3E_eq (x161, x162), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_eq (x161, x162) -> false
    | Z3E_minus (x151, x152), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_minus (x151, x152) -> false
    | Z3E_mod (x141, x142), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_mod (x141, x142) -> false
    | Z3E_div (x131, x132), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_div (x131, x132) -> false
    | Z3E_times (x121, x122), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_times (x121, x122) -> false
    | Z3E_plus (x111, x112), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_plus (x111, x112) -> false
    | Z3E_geq (x101, x102), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_geq (x101, x102) -> false
    | Z3E_leq (x91, x92), Z3E_string x25 -> false
    | Z3E_string x25, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_leq (x91, x92) -> false
    | Z3E_len x8, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_len x8 -> false
    | Z3E_bitzero, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_bitzero -> false
    | Z3E_bitone, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_bitone -> false
    | Z3E_bitone, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_bitone -> false
    | Z3E_bitone, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_bitone -> false
    | Z3E_bitone, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_bitone -> false
    | Z3E_bitone, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_bitone -> false
    | Z3E_bitone, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_bitone -> false
    | Z3E_bitone, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_bitone -> false
    | Z3E_bitone, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_bitone -> false
    | Z3E_bitone, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_bitone -> false
    | Z3E_bitone, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_bitone -> false
    | Z3E_bitone, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_bitone -> false
    | Z3E_bitone, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_bitone -> false
    | Z3E_bitone, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_bitone -> false
    | Z3E_bitone, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_bitone -> false
    | Z3E_bitone, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_bitone -> false
    | Z3E_bitone, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_bitone -> false
    | Z3E_bitone, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_bitone -> false
    | Z3E_bitone, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_bitone -> false
    | Z3E_bitone, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_bitone -> false
    | Z3E_unit, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_unit -> false
    | Z3E_unit, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_unit -> false
    | Z3E_unit, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_unit -> false
    | Z3E_unit, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_unit -> false
    | Z3E_unit, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_unit -> false
    | Z3E_unit, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_unit -> false
    | Z3E_unit, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_unit -> false
    | Z3E_unit, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_unit -> false
    | Z3E_unit, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_unit -> false
    | Z3E_unit, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_unit -> false
    | Z3E_unit, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_unit -> false
    | Z3E_unit, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_unit -> false
    | Z3E_unit, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_unit -> false
    | Z3E_unit, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_unit -> false
    | Z3E_unit, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_unit -> false
    | Z3E_unit, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_unit -> false
    | Z3E_unit, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_unit -> false
    | Z3E_unit, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_unit -> false
    | Z3E_unit, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_unit -> false
    | Z3E_unit, Z3E_bitone -> false
    | Z3E_bitone, Z3E_unit -> false
    | Z3E_false, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_false -> false
    | Z3E_false, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_false -> false
    | Z3E_false, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_false -> false
    | Z3E_false, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_false -> false
    | Z3E_false, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_false -> false
    | Z3E_false, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_false -> false
    | Z3E_false, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_false -> false
    | Z3E_false, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_false -> false
    | Z3E_false, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_false -> false
    | Z3E_false, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_false -> false
    | Z3E_false, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_false -> false
    | Z3E_false, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_false -> false
    | Z3E_false, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_false -> false
    | Z3E_false, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_false -> false
    | Z3E_false, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_false -> false
    | Z3E_false, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_false -> false
    | Z3E_false, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_false -> false
    | Z3E_false, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_false -> false
    | Z3E_false, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_false -> false
    | Z3E_false, Z3E_bitone -> false
    | Z3E_bitone, Z3E_false -> false
    | Z3E_false, Z3E_unit -> false
    | Z3E_unit, Z3E_false -> false
    | Z3E_true, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_true -> false
    | Z3E_true, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_true -> false
    | Z3E_true, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_true -> false
    | Z3E_true, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_true -> false
    | Z3E_true, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_true -> false
    | Z3E_true, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_true -> false
    | Z3E_true, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_true -> false
    | Z3E_true, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_true -> false
    | Z3E_true, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_true -> false
    | Z3E_true, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_true -> false
    | Z3E_true, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_true -> false
    | Z3E_true, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_true -> false
    | Z3E_true, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_true -> false
    | Z3E_true, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_true -> false
    | Z3E_true, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_true -> false
    | Z3E_true, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_true -> false
    | Z3E_true, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_true -> false
    | Z3E_true, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_true -> false
    | Z3E_true, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_true -> false
    | Z3E_true, Z3E_bitone -> false
    | Z3E_bitone, Z3E_true -> false
    | Z3E_true, Z3E_unit -> false
    | Z3E_unit, Z3E_true -> false
    | Z3E_true, Z3E_false -> false
    | Z3E_false, Z3E_true -> false
    | Z3E_var x2, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_bitone -> false
    | Z3E_bitone, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_unit -> false
    | Z3E_unit, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_false -> false
    | Z3E_false, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_true -> false
    | Z3E_true, Z3E_var x2 -> false
    | Z3E_num x1, Z3E_string x25 -> false
    | Z3E_string x25, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_proj (x241, x242) -> false
    | Z3E_proj (x241, x242), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_concat x23 -> false
    | Z3E_concat x23, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_constr (x221, x222) -> false
    | Z3E_constr (x221, x222), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_bitvec x21 -> false
    | Z3E_bitvec x21, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_neq (x201, x202) -> false
    | Z3E_neq (x201, x202), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_or (x191, x192) -> false
    | Z3E_or (x191, x192), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_and (x181, x182) -> false
    | Z3E_and (x181, x182), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_bitone -> false
    | Z3E_bitone, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_unit -> false
    | Z3E_unit, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_false -> false
    | Z3E_false, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_true -> false
    | Z3E_true, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_num x1 -> false
    | Z3E_string x25, Z3E_string y25 -> ((x25 : string) = y25)
    | Z3E_proj (x241, x242), Z3E_proj (y241, y242) ->
        ((x241 : string) = y241) && equal_z3_expra x242 y242
    | Z3E_concat x23, Z3E_concat y23 ->
        Lista.equal_list (equal_z3_expr ()) x23 y23
    | Z3E_constr (x221, x222), Z3E_constr (y221, y222) ->
        ((x221 : string) = y221) &&
          Lista.equal_list (equal_z3_expr ()) x222 y222
    | Z3E_bitvec x21, Z3E_bitvec y21 -> ((x21 : string) = y21)
    | Z3E_neq (x201, x202), Z3E_neq (y201, y202) ->
        equal_z3_expra x201 y201 && equal_z3_expra x202 y202
    | Z3E_or (x191, x192), Z3E_or (y191, y192) ->
        equal_z3_expra x191 y191 && equal_z3_expra x192 y192
    | Z3E_and (x181, x182), Z3E_and (y181, y182) ->
        equal_z3_expra x181 y181 && equal_z3_expra x182 y182
    | Z3E_not x17, Z3E_not y17 -> equal_z3_expra x17 y17
    | Z3E_eq (x161, x162), Z3E_eq (y161, y162) ->
        equal_z3_expra x161 y161 && equal_z3_expra x162 y162
    | Z3E_minus (x151, x152), Z3E_minus (y151, y152) ->
        equal_z3_expra x151 y151 && equal_z3_expra x152 y152
    | Z3E_mod (x141, x142), Z3E_mod (y141, y142) ->
        equal_z3_expra x141 y141 && equal_z3_expra x142 y142
    | Z3E_div (x131, x132), Z3E_div (y131, y132) ->
        equal_z3_expra x131 y131 && equal_z3_expra x132 y132
    | Z3E_times (x121, x122), Z3E_times (y121, y122) ->
        equal_z3_expra x121 y121 && equal_z3_expra x122 y122
    | Z3E_plus (x111, x112), Z3E_plus (y111, y112) ->
        equal_z3_expra x111 y111 && equal_z3_expra x112 y112
    | Z3E_geq (x101, x102), Z3E_geq (y101, y102) ->
        equal_z3_expra x101 y101 && equal_z3_expra x102 y102
    | Z3E_leq (x91, x92), Z3E_leq (y91, y92) ->
        equal_z3_expra x91 y91 && equal_z3_expra x92 y92
    | Z3E_len x8, Z3E_len y8 -> equal_z3_expra x8 y8
    | Z3E_var x2, Z3E_var y2 -> ((x2 : string) = y2)
    | Z3E_num x1, Z3E_num y1 -> Z.equal x1 y1
    | Z3E_bitzero, Z3E_bitzero -> true
    | Z3E_bitone, Z3E_bitone -> true
    | Z3E_unit, Z3E_unit -> true
    | Z3E_false, Z3E_false -> true
    | Z3E_true, Z3E_true -> true;;
let equal_z3_expr = equal_z3_expr ();;

type z3_bool_expr = Z3BE_true | Z3BE_false | Z3BE_not of z3_bool_expr |
  Z3BE_and of z3_bool_expr list | Z3BE_or of z3_bool_expr list |
  Z3BE_eq of z3_expr * z3_expr | Z3BE_leq of z3_expr * z3_expr |
  Z3BE_implies of z3_bool_expr * z3_bool_expr;;

let rec equal_z3_bool_expr () =
  ({HOL.equal = equal_z3_bool_expra} : z3_bool_expr HOL.equal)
and equal_z3_bool_expra
  x0 x1 = match x0, x1 with
    Z3BE_leq (x71, x72), Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_leq (x71, x72) -> false
    | Z3BE_eq (x61, x62), Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_eq (x61, x62) -> false
    | Z3BE_or x5, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_or x5 -> false
    | Z3BE_and x4, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_and x4 -> false
    | Z3BE_not x3, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_not x3 -> false
    | Z3BE_false, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_false -> false
    | Z3BE_false, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_false -> false
    | Z3BE_false, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_false -> false
    | Z3BE_false, Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_false -> false
    | Z3BE_false, Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_false -> false
    | Z3BE_false, Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_false -> false
    | Z3BE_true, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_true -> false
    | Z3BE_true, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_true -> false
    | Z3BE_true, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_true -> false
    | Z3BE_true, Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_true -> false
    | Z3BE_true, Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_true -> false
    | Z3BE_true, Z3BE_not x3 -> false
    | Z3BE_not x3, Z3BE_true -> false
    | Z3BE_true, Z3BE_false -> false
    | Z3BE_false, Z3BE_true -> false
    | Z3BE_implies (x81, x82), Z3BE_implies (y81, y82) ->
        equal_z3_bool_expra x81 y81 && equal_z3_bool_expra x82 y82
    | Z3BE_leq (x71, x72), Z3BE_leq (y71, y72) ->
        equal_z3_expra x71 y71 && equal_z3_expra x72 y72
    | Z3BE_eq (x61, x62), Z3BE_eq (y61, y62) ->
        equal_z3_expra x61 y61 && equal_z3_expra x62 y62
    | Z3BE_or x5, Z3BE_or y5 -> Lista.equal_list (equal_z3_bool_expr ()) x5 y5
    | Z3BE_and x4, Z3BE_and y4 -> Lista.equal_list (equal_z3_bool_expr ()) x4 y4
    | Z3BE_not x3, Z3BE_not y3 -> equal_z3_bool_expra x3 y3
    | Z3BE_false, Z3BE_false -> true
    | Z3BE_true, Z3BE_true -> true;;
let equal_z3_bool_expr = equal_z3_bool_expr ();;

type z3_type = Z3T_int | Z3T_bool | Z3T_unit | Z3T_array of z3_type * z3_type |
  Z3T_dt of string * z3_type list | Z3T_sort of string | Z3T_string;;

type z3_type_var = Z3TV_tv_type of z3_type | Z3TV_tv_var of Z.t;;

type z3_constr = Z3C_ty_constr of string * (string * z3_type_var) list;;

type z3_decl = Z3D_decl_fun | Z3D_decl_const of string * z3_type |
  Z3D_decl_datatype of string * z3_type_var list * z3_constr list;;

end;; (*struct Z3*)

module Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if HOL.eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

end;; (*struct Map*)

module AList : sig
  val update : 'a HOL.equal -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
  val merge : 'a HOL.equal -> ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
end = struct

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if HOL.eq _A (Product_Type.fst p) k then (k, v) :: ps
          else p :: update _A k v ps);;

let rec merge _A qs ps = Lista.foldr (fun (a, b) -> update _A a b) ps qs;;

end;; (*struct AList*)

module Debug : sig
  val trace : string -> unit
end = struct

let rec trace s = ();;

end;; (*struct Debug*)

module Finite_Map : sig
  type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list
  val fmadd : 'a HOL.equal -> ('a, 'b) fmap -> ('a, 'b) fmap -> ('a, 'b) fmap
  val fmupd : 'a HOL.equal -> 'a -> 'b -> ('a, 'b) fmap -> ('a, 'b) fmap
  val fmempty : ('a, 'b) fmap
  val fmlookup : 'a HOL.equal -> ('a, 'b) fmap -> 'a -> 'b option
end = struct

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (AList.merge _A m n);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec fmlookup _A (Fmap_of_list m) = Map.map_of _A m;;

end;; (*struct Finite_Map*)

module Stringa : sig
  val equal_literal : string HOL.equal
  type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool
  val integer_of_char : char -> Z.t
  val implode : char list -> string
  val char_of_integer : Z.t -> char
  val explode : string -> char list
  val equal_char : char -> char -> bool
end = struct

let equal_literal =
  ({HOL.equal = (fun a b -> ((a : string) = b))} : string HOL.equal);;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Z.add (Z.mul
            (Z.add
              (Z.mul
                (Z.add
                  (Z.mul
                    (Z.add
                      (Z.mul
                        (Z.add
                          (Z.mul
                            (Z.add
                              (Z.mul
                                (Z.add
                                  (Z.mul
                                    (Arith.of_bool Arith.zero_neq_one_integer
                                      b7)
                                    (Z.of_int 2))
                                  (Arith.of_bool Arith.zero_neq_one_integer b6))
                                (Z.of_int 2))
                              (Arith.of_bool Arith.zero_neq_one_integer b5))
                            (Z.of_int 2))
                          (Arith.of_bool Arith.zero_neq_one_integer b4))
                        (Z.of_int 2))
                      (Arith.of_bool Arith.zero_neq_one_integer b3))
                    (Z.of_int 2))
                  (Arith.of_bool Arith.zero_neq_one_integer b2))
                (Z.of_int 2))
              (Arith.of_bool Arith.zero_neq_one_integer b1))
            (Z.of_int 2))
      (Arith.of_bool Arith.zero_neq_one_integer b0);;

let rec implode
  cs = (let xs = (Lista.map integer_of_char
                   cs)
      and chr k =
        let l = Z.to_int k
          in if 0 <= l && l < 128
          then Char.chr l
          else failwith "Non-ASCII character in literal"
      in String.init (List.length xs) (List.nth (List.map chr xs)));;

let rec char_of_integer
  k = (let (q0, b0) = Arith.bit_cut_integer k in
       let (q1, b1) = Arith.bit_cut_integer q0 in
       let (q2, b2) = Arith.bit_cut_integer q1 in
       let (q3, b3) = Arith.bit_cut_integer q2 in
       let (q4, b4) = Arith.bit_cut_integer q3 in
       let (q5, b5) = Arith.bit_cut_integer q4 in
       let (q6, b6) = Arith.bit_cut_integer q5 in
       let a = Arith.bit_cut_integer q6 in
       let (_, aa) = a in
        Chara (b0, b1, b2, b3, b4, b5, b6, aa));;

let rec explode
  s = Lista.map char_of_integer
        (let s = s in let rec exp i l = if i < 0 then l else exp (i - 1) (let k = Char.code (String.get s i) in
      if k < 128 then Z.of_int k :: l else failwith "Non-ASCII character in literal") in exp (String.length s - 1) []);;

let rec equal_char
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    Product_Type.equal_bool x1 y1 &&
      (Product_Type.equal_bool x2 y2 &&
        (Product_Type.equal_bool x3 y3 &&
          (Product_Type.equal_bool x4 y4 &&
            (Product_Type.equal_bool x5 y5 &&
              (Product_Type.equal_bool x6 y6 &&
                (Product_Type.equal_bool x7 y7 &&
                  Product_Type.equal_bool x8 y8))))));;

end;; (*struct Stringa*)

module SyntaxVCT : sig
  type order = Ord_inc | Ord_dec | Ord_def
  val equal_order : order -> order -> bool
  type xp = VNamed of string | VIndex
  type uop = Len | Exp | Neg | Not
  type bop = Plus | Minus | Times | Div | Mod | LEq | LT | GT | GEq | Eq | And |
    Or | NEq
  type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
    L_string of string | L_undef | L_real of string
  type vp = V_lit of lit | V_var of xp | V_vec of vp list | V_list of vp list |
    V_cons of vp * vp | V_constr of string * vp | V_record of (string * vp) list
    | V_tuple of vp list | V_proj of string * vp
  type cep = CE_val of vp | CE_bop of bop * cep * cep | CE_many_plus of cep list
    | CE_uop of uop * cep | CE_proj of string * cep |
    CE_field_access of xp * string
  type cp = C_true | C_false | C_conj of cp * cp | C_conj_many of cp list |
    C_disj of cp * cp | C_not of cp | C_eq of cep * cep | C_leq of cep * cep |
    C_imp of cp * cp
  type bp = B_var of string | B_tid of string | B_int | B_bool | B_bit | B_unit
    | B_real | B_vec of order * bp | B_list of bp | B_tuple of bp list |
    B_union of string * (string * tau) list | B_record of (string * bp) list |
    B_undef | B_reg | B_string | B_exception | B_finite_set of Z.t list
  and tau = T_refined_type of xp * bp * cp
  val equal_xpa : xp -> xp -> bool
  val equal_uop : uop -> uop -> bool
  val equal_bop : bop -> bop -> bool
  val equal_lita : lit -> lit -> bool
  val equal_vpa : vp -> vp -> bool
  val equal_vp : vp HOL.equal
  val equal_cepa : cep -> cep -> bool
  val equal_cep : cep HOL.equal
  val equal_cpa : cp -> cp -> bool
  val equal_cp : cp HOL.equal
  val equal_bp : bp HOL.equal
  val equal_bpa : bp -> bp -> bool
  val equal_taua : tau -> tau -> bool
  val equal_tau : tau HOL.equal
  val equal_xp : xp HOL.equal
  val equal_lit : lit HOL.equal
  type ap = A_monotype of tau | A_function of xp * bp * cp * tau
  type bsub = BS_empty | BS_cons of bsub * bp * string
  val subst_vp : vp -> xp -> vp -> vp
  val subst_vp_list_V_vec : vp -> xp -> vp list -> vp list
  val subst_vp_list_V_list : vp -> xp -> vp list -> vp list
  val subst_vp_list_V_tuple : vp -> xp -> vp list -> vp list
  val subst_field_vp_V_record : vp -> xp -> string * vp -> string * vp
  val subst_field_vp_list_V_record :
    vp -> xp -> (string * vp) list -> (string * vp) list
  val subst_cep : vp -> xp -> cep -> cep
  val subst_cep_list : vp -> xp -> cep list -> cep list
  val subst_cp : vp -> xp -> cp -> cp
  val subst_cp_list : vp -> xp -> cp list -> cp list
  val tsubst_bp : bp -> string -> bp -> bp
  val tsubst_tp : bp -> string -> tau -> tau
  val tsubst_ctor_tau : bp -> string -> string * tau -> string * tau
  val tsubst_ctor_tau_list :
    bp -> string -> (string * tau) list -> (string * tau) list
  val tsubst_bp_list : bp -> string -> bp list -> bp list
  val tsubst_field_bp : bp -> string -> string * bp -> string * bp
  val tsubst_field_bp_list :
    bp -> string -> (string * bp) list -> (string * bp) list
end = struct

type order = Ord_inc | Ord_dec | Ord_def;;

let rec equal_order x0 x1 = match x0, x1 with Ord_dec, Ord_def -> false
                      | Ord_def, Ord_dec -> false
                      | Ord_inc, Ord_def -> false
                      | Ord_def, Ord_inc -> false
                      | Ord_inc, Ord_dec -> false
                      | Ord_dec, Ord_inc -> false
                      | Ord_def, Ord_def -> true
                      | Ord_dec, Ord_dec -> true
                      | Ord_inc, Ord_inc -> true;;

type xp = VNamed of string | VIndex;;

type uop = Len | Exp | Neg | Not;;

type bop = Plus | Minus | Times | Div | Mod | LEq | LT | GT | GEq | Eq | And |
  Or | NEq;;

type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
  L_string of string | L_undef | L_real of string;;

type vp = V_lit of lit | V_var of xp | V_vec of vp list | V_list of vp list |
  V_cons of vp * vp | V_constr of string * vp | V_record of (string * vp) list |
  V_tuple of vp list | V_proj of string * vp;;

type cep = CE_val of vp | CE_bop of bop * cep * cep | CE_many_plus of cep list |
  CE_uop of uop * cep | CE_proj of string * cep |
  CE_field_access of xp * string;;

type cp = C_true | C_false | C_conj of cp * cp | C_conj_many of cp list |
  C_disj of cp * cp | C_not of cp | C_eq of cep * cep | C_leq of cep * cep |
  C_imp of cp * cp;;

type bp = B_var of string | B_tid of string | B_int | B_bool | B_bit | B_unit |
  B_real | B_vec of order * bp | B_list of bp | B_tuple of bp list |
  B_union of string * (string * tau) list | B_record of (string * bp) list |
  B_undef | B_reg | B_string | B_exception | B_finite_set of Z.t list
and tau = T_refined_type of xp * bp * cp;;

let rec equal_xpa x0 x1 = match x0, x1 with VNamed x1, VIndex -> false
                    | VIndex, VNamed x1 -> false
                    | VNamed x1, VNamed y1 -> ((x1 : string) = y1)
                    | VIndex, VIndex -> true;;

let rec equal_uop x0 x1 = match x0, x1 with Neg, Not -> false
                    | Not, Neg -> false
                    | Exp, Not -> false
                    | Not, Exp -> false
                    | Exp, Neg -> false
                    | Neg, Exp -> false
                    | Len, Not -> false
                    | Not, Len -> false
                    | Len, Neg -> false
                    | Neg, Len -> false
                    | Len, Exp -> false
                    | Exp, Len -> false
                    | Not, Not -> true
                    | Neg, Neg -> true
                    | Exp, Exp -> true
                    | Len, Len -> true;;

let rec equal_bop x0 x1 = match x0, x1 with Or, NEq -> false
                    | NEq, Or -> false
                    | And, NEq -> false
                    | NEq, And -> false
                    | And, Or -> false
                    | Or, And -> false
                    | Eq, NEq -> false
                    | NEq, Eq -> false
                    | Eq, Or -> false
                    | Or, Eq -> false
                    | Eq, And -> false
                    | And, Eq -> false
                    | GEq, NEq -> false
                    | NEq, GEq -> false
                    | GEq, Or -> false
                    | Or, GEq -> false
                    | GEq, And -> false
                    | And, GEq -> false
                    | GEq, Eq -> false
                    | Eq, GEq -> false
                    | GT, NEq -> false
                    | NEq, GT -> false
                    | GT, Or -> false
                    | Or, GT -> false
                    | GT, And -> false
                    | And, GT -> false
                    | GT, Eq -> false
                    | Eq, GT -> false
                    | GT, GEq -> false
                    | GEq, GT -> false
                    | LT, NEq -> false
                    | NEq, LT -> false
                    | LT, Or -> false
                    | Or, LT -> false
                    | LT, And -> false
                    | And, LT -> false
                    | LT, Eq -> false
                    | Eq, LT -> false
                    | LT, GEq -> false
                    | GEq, LT -> false
                    | LT, GT -> false
                    | GT, LT -> false
                    | LEq, NEq -> false
                    | NEq, LEq -> false
                    | LEq, Or -> false
                    | Or, LEq -> false
                    | LEq, And -> false
                    | And, LEq -> false
                    | LEq, Eq -> false
                    | Eq, LEq -> false
                    | LEq, GEq -> false
                    | GEq, LEq -> false
                    | LEq, GT -> false
                    | GT, LEq -> false
                    | LEq, LT -> false
                    | LT, LEq -> false
                    | Mod, NEq -> false
                    | NEq, Mod -> false
                    | Mod, Or -> false
                    | Or, Mod -> false
                    | Mod, And -> false
                    | And, Mod -> false
                    | Mod, Eq -> false
                    | Eq, Mod -> false
                    | Mod, GEq -> false
                    | GEq, Mod -> false
                    | Mod, GT -> false
                    | GT, Mod -> false
                    | Mod, LT -> false
                    | LT, Mod -> false
                    | Mod, LEq -> false
                    | LEq, Mod -> false
                    | Div, NEq -> false
                    | NEq, Div -> false
                    | Div, Or -> false
                    | Or, Div -> false
                    | Div, And -> false
                    | And, Div -> false
                    | Div, Eq -> false
                    | Eq, Div -> false
                    | Div, GEq -> false
                    | GEq, Div -> false
                    | Div, GT -> false
                    | GT, Div -> false
                    | Div, LT -> false
                    | LT, Div -> false
                    | Div, LEq -> false
                    | LEq, Div -> false
                    | Div, Mod -> false
                    | Mod, Div -> false
                    | Times, NEq -> false
                    | NEq, Times -> false
                    | Times, Or -> false
                    | Or, Times -> false
                    | Times, And -> false
                    | And, Times -> false
                    | Times, Eq -> false
                    | Eq, Times -> false
                    | Times, GEq -> false
                    | GEq, Times -> false
                    | Times, GT -> false
                    | GT, Times -> false
                    | Times, LT -> false
                    | LT, Times -> false
                    | Times, LEq -> false
                    | LEq, Times -> false
                    | Times, Mod -> false
                    | Mod, Times -> false
                    | Times, Div -> false
                    | Div, Times -> false
                    | Minus, NEq -> false
                    | NEq, Minus -> false
                    | Minus, Or -> false
                    | Or, Minus -> false
                    | Minus, And -> false
                    | And, Minus -> false
                    | Minus, Eq -> false
                    | Eq, Minus -> false
                    | Minus, GEq -> false
                    | GEq, Minus -> false
                    | Minus, GT -> false
                    | GT, Minus -> false
                    | Minus, LT -> false
                    | LT, Minus -> false
                    | Minus, LEq -> false
                    | LEq, Minus -> false
                    | Minus, Mod -> false
                    | Mod, Minus -> false
                    | Minus, Div -> false
                    | Div, Minus -> false
                    | Minus, Times -> false
                    | Times, Minus -> false
                    | Plus, NEq -> false
                    | NEq, Plus -> false
                    | Plus, Or -> false
                    | Or, Plus -> false
                    | Plus, And -> false
                    | And, Plus -> false
                    | Plus, Eq -> false
                    | Eq, Plus -> false
                    | Plus, GEq -> false
                    | GEq, Plus -> false
                    | Plus, GT -> false
                    | GT, Plus -> false
                    | Plus, LT -> false
                    | LT, Plus -> false
                    | Plus, LEq -> false
                    | LEq, Plus -> false
                    | Plus, Mod -> false
                    | Mod, Plus -> false
                    | Plus, Div -> false
                    | Div, Plus -> false
                    | Plus, Times -> false
                    | Times, Plus -> false
                    | Plus, Minus -> false
                    | Minus, Plus -> false
                    | NEq, NEq -> true
                    | Or, Or -> true
                    | And, And -> true
                    | Eq, Eq -> true
                    | GEq, GEq -> true
                    | GT, GT -> true
                    | LT, LT -> true
                    | LEq, LEq -> true
                    | Mod, Mod -> true
                    | Div, Div -> true
                    | Times, Times -> true
                    | Minus, Minus -> true
                    | Plus, Plus -> true;;

let rec equal_lita x0 x1 = match x0, x1 with L_undef, L_real x9 -> false
                     | L_real x9, L_undef -> false
                     | L_string x7, L_real x9 -> false
                     | L_real x9, L_string x7 -> false
                     | L_string x7, L_undef -> false
                     | L_undef, L_string x7 -> false
                     | L_num x6, L_real x9 -> false
                     | L_real x9, L_num x6 -> false
                     | L_num x6, L_undef -> false
                     | L_undef, L_num x6 -> false
                     | L_num x6, L_string x7 -> false
                     | L_string x7, L_num x6 -> false
                     | L_false, L_real x9 -> false
                     | L_real x9, L_false -> false
                     | L_false, L_undef -> false
                     | L_undef, L_false -> false
                     | L_false, L_string x7 -> false
                     | L_string x7, L_false -> false
                     | L_false, L_num x6 -> false
                     | L_num x6, L_false -> false
                     | L_true, L_real x9 -> false
                     | L_real x9, L_true -> false
                     | L_true, L_undef -> false
                     | L_undef, L_true -> false
                     | L_true, L_string x7 -> false
                     | L_string x7, L_true -> false
                     | L_true, L_num x6 -> false
                     | L_num x6, L_true -> false
                     | L_true, L_false -> false
                     | L_false, L_true -> false
                     | L_one, L_real x9 -> false
                     | L_real x9, L_one -> false
                     | L_one, L_undef -> false
                     | L_undef, L_one -> false
                     | L_one, L_string x7 -> false
                     | L_string x7, L_one -> false
                     | L_one, L_num x6 -> false
                     | L_num x6, L_one -> false
                     | L_one, L_false -> false
                     | L_false, L_one -> false
                     | L_one, L_true -> false
                     | L_true, L_one -> false
                     | L_zero, L_real x9 -> false
                     | L_real x9, L_zero -> false
                     | L_zero, L_undef -> false
                     | L_undef, L_zero -> false
                     | L_zero, L_string x7 -> false
                     | L_string x7, L_zero -> false
                     | L_zero, L_num x6 -> false
                     | L_num x6, L_zero -> false
                     | L_zero, L_false -> false
                     | L_false, L_zero -> false
                     | L_zero, L_true -> false
                     | L_true, L_zero -> false
                     | L_zero, L_one -> false
                     | L_one, L_zero -> false
                     | L_unit, L_real x9 -> false
                     | L_real x9, L_unit -> false
                     | L_unit, L_undef -> false
                     | L_undef, L_unit -> false
                     | L_unit, L_string x7 -> false
                     | L_string x7, L_unit -> false
                     | L_unit, L_num x6 -> false
                     | L_num x6, L_unit -> false
                     | L_unit, L_false -> false
                     | L_false, L_unit -> false
                     | L_unit, L_true -> false
                     | L_true, L_unit -> false
                     | L_unit, L_one -> false
                     | L_one, L_unit -> false
                     | L_unit, L_zero -> false
                     | L_zero, L_unit -> false
                     | L_real x9, L_real y9 -> ((x9 : string) = y9)
                     | L_string x7, L_string y7 -> ((x7 : string) = y7)
                     | L_num x6, L_num y6 -> Z.equal x6 y6
                     | L_undef, L_undef -> true
                     | L_false, L_false -> true
                     | L_true, L_true -> true
                     | L_one, L_one -> true
                     | L_zero, L_zero -> true
                     | L_unit, L_unit -> true;;

let rec equal_vpa
  x0 x1 = match x0, x1 with V_tuple x8, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_tuple x8 -> false
    | V_record x7, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_record x7 -> false
    | V_record x7, V_tuple x8 -> false
    | V_tuple x8, V_record x7 -> false
    | V_constr (x61, x62), V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_tuple x8 -> false
    | V_tuple x8, V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_record x7 -> false
    | V_record x7, V_constr (x61, x62) -> false
    | V_cons (x51, x52), V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_tuple x8 -> false
    | V_tuple x8, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_record x7 -> false
    | V_record x7, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_cons (x51, x52) -> false
    | V_list x4, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_list x4 -> false
    | V_list x4, V_tuple x8 -> false
    | V_tuple x8, V_list x4 -> false
    | V_list x4, V_record x7 -> false
    | V_record x7, V_list x4 -> false
    | V_list x4, V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_list x4 -> false
    | V_list x4, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_list x4 -> false
    | V_vec x3, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_vec x3 -> false
    | V_vec x3, V_tuple x8 -> false
    | V_tuple x8, V_vec x3 -> false
    | V_vec x3, V_record x7 -> false
    | V_record x7, V_vec x3 -> false
    | V_vec x3, V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_vec x3 -> false
    | V_vec x3, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_vec x3 -> false
    | V_vec x3, V_list x4 -> false
    | V_list x4, V_vec x3 -> false
    | V_var x2, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_var x2 -> false
    | V_var x2, V_tuple x8 -> false
    | V_tuple x8, V_var x2 -> false
    | V_var x2, V_record x7 -> false
    | V_record x7, V_var x2 -> false
    | V_var x2, V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_var x2 -> false
    | V_var x2, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_var x2 -> false
    | V_var x2, V_list x4 -> false
    | V_list x4, V_var x2 -> false
    | V_var x2, V_vec x3 -> false
    | V_vec x3, V_var x2 -> false
    | V_lit x1, V_proj (x91, x92) -> false
    | V_proj (x91, x92), V_lit x1 -> false
    | V_lit x1, V_tuple x8 -> false
    | V_tuple x8, V_lit x1 -> false
    | V_lit x1, V_record x7 -> false
    | V_record x7, V_lit x1 -> false
    | V_lit x1, V_constr (x61, x62) -> false
    | V_constr (x61, x62), V_lit x1 -> false
    | V_lit x1, V_cons (x51, x52) -> false
    | V_cons (x51, x52), V_lit x1 -> false
    | V_lit x1, V_list x4 -> false
    | V_list x4, V_lit x1 -> false
    | V_lit x1, V_vec x3 -> false
    | V_vec x3, V_lit x1 -> false
    | V_lit x1, V_var x2 -> false
    | V_var x2, V_lit x1 -> false
    | V_proj (x91, x92), V_proj (y91, y92) ->
        ((x91 : string) = y91) && equal_vpa x92 y92
    | V_tuple x8, V_tuple y8 -> Lista.equal_list (equal_vp ()) x8 y8
    | V_record x7, V_record y7 ->
        Lista.equal_list
          (Product_Type.equal_prod Stringa.equal_literal (equal_vp ())) x7 y7
    | V_constr (x61, x62), V_constr (y61, y62) ->
        ((x61 : string) = y61) && equal_vpa x62 y62
    | V_cons (x51, x52), V_cons (y51, y52) ->
        equal_vpa x51 y51 && equal_vpa x52 y52
    | V_list x4, V_list y4 -> Lista.equal_list (equal_vp ()) x4 y4
    | V_vec x3, V_vec y3 -> Lista.equal_list (equal_vp ()) x3 y3
    | V_var x2, V_var y2 -> equal_xpa x2 y2
    | V_lit x1, V_lit y1 -> equal_lita x1 y1
and equal_vp () = ({HOL.equal = equal_vpa} : vp HOL.equal);;
let equal_vp = equal_vp ();;

let rec equal_cepa
  x0 x1 = match x0, x1 with
    CE_proj (x51, x52), CE_field_access (x61, x62) -> false
    | CE_field_access (x61, x62), CE_proj (x51, x52) -> false
    | CE_uop (x41, x42), CE_field_access (x61, x62) -> false
    | CE_field_access (x61, x62), CE_uop (x41, x42) -> false
    | CE_uop (x41, x42), CE_proj (x51, x52) -> false
    | CE_proj (x51, x52), CE_uop (x41, x42) -> false
    | CE_many_plus x3, CE_field_access (x61, x62) -> false
    | CE_field_access (x61, x62), CE_many_plus x3 -> false
    | CE_many_plus x3, CE_proj (x51, x52) -> false
    | CE_proj (x51, x52), CE_many_plus x3 -> false
    | CE_many_plus x3, CE_uop (x41, x42) -> false
    | CE_uop (x41, x42), CE_many_plus x3 -> false
    | CE_bop (x21, x22, x23), CE_field_access (x61, x62) -> false
    | CE_field_access (x61, x62), CE_bop (x21, x22, x23) -> false
    | CE_bop (x21, x22, x23), CE_proj (x51, x52) -> false
    | CE_proj (x51, x52), CE_bop (x21, x22, x23) -> false
    | CE_bop (x21, x22, x23), CE_uop (x41, x42) -> false
    | CE_uop (x41, x42), CE_bop (x21, x22, x23) -> false
    | CE_bop (x21, x22, x23), CE_many_plus x3 -> false
    | CE_many_plus x3, CE_bop (x21, x22, x23) -> false
    | CE_val x1, CE_field_access (x61, x62) -> false
    | CE_field_access (x61, x62), CE_val x1 -> false
    | CE_val x1, CE_proj (x51, x52) -> false
    | CE_proj (x51, x52), CE_val x1 -> false
    | CE_val x1, CE_uop (x41, x42) -> false
    | CE_uop (x41, x42), CE_val x1 -> false
    | CE_val x1, CE_many_plus x3 -> false
    | CE_many_plus x3, CE_val x1 -> false
    | CE_val x1, CE_bop (x21, x22, x23) -> false
    | CE_bop (x21, x22, x23), CE_val x1 -> false
    | CE_field_access (x61, x62), CE_field_access (y61, y62) ->
        equal_xpa x61 y61 && ((x62 : string) = y62)
    | CE_proj (x51, x52), CE_proj (y51, y52) ->
        ((x51 : string) = y51) && equal_cepa x52 y52
    | CE_uop (x41, x42), CE_uop (y41, y42) ->
        equal_uop x41 y41 && equal_cepa x42 y42
    | CE_many_plus x3, CE_many_plus y3 -> Lista.equal_list (equal_cep ()) x3 y3
    | CE_bop (x21, x22, x23), CE_bop (y21, y22, y23) ->
        equal_bop x21 y21 && (equal_cepa x22 y22 && equal_cepa x23 y23)
    | CE_val x1, CE_val y1 -> equal_vpa x1 y1
and equal_cep () = ({HOL.equal = equal_cepa} : cep HOL.equal);;
let equal_cep = equal_cep ();;

let rec equal_cpa
  x0 x1 = match x0, x1 with C_leq (x81, x82), C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_leq (x81, x82) -> false
    | C_eq (x71, x72), C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_eq (x71, x72) -> false
    | C_not x6, C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_not x6 -> false
    | C_not x6, C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_not x6 -> false
    | C_not x6, C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_not x6 -> false
    | C_disj (x51, x52), C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_not x6 -> false
    | C_not x6, C_disj (x51, x52) -> false
    | C_conj_many x4, C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_conj_many x4 -> false
    | C_conj_many x4, C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_conj_many x4 -> false
    | C_conj_many x4, C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_conj_many x4 -> false
    | C_conj_many x4, C_not x6 -> false
    | C_not x6, C_conj_many x4 -> false
    | C_conj_many x4, C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_conj_many x4 -> false
    | C_conj (x31, x32), C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_not x6 -> false
    | C_not x6, C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_conj_many x4 -> false
    | C_conj_many x4, C_conj (x31, x32) -> false
    | C_false, C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_false -> false
    | C_false, C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_false -> false
    | C_false, C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_false -> false
    | C_false, C_not x6 -> false
    | C_not x6, C_false -> false
    | C_false, C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_false -> false
    | C_false, C_conj_many x4 -> false
    | C_conj_many x4, C_false -> false
    | C_false, C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_false -> false
    | C_true, C_imp (x91, x92) -> false
    | C_imp (x91, x92), C_true -> false
    | C_true, C_leq (x81, x82) -> false
    | C_leq (x81, x82), C_true -> false
    | C_true, C_eq (x71, x72) -> false
    | C_eq (x71, x72), C_true -> false
    | C_true, C_not x6 -> false
    | C_not x6, C_true -> false
    | C_true, C_disj (x51, x52) -> false
    | C_disj (x51, x52), C_true -> false
    | C_true, C_conj_many x4 -> false
    | C_conj_many x4, C_true -> false
    | C_true, C_conj (x31, x32) -> false
    | C_conj (x31, x32), C_true -> false
    | C_true, C_false -> false
    | C_false, C_true -> false
    | C_imp (x91, x92), C_imp (y91, y92) ->
        equal_cpa x91 y91 && equal_cpa x92 y92
    | C_leq (x81, x82), C_leq (y81, y82) ->
        equal_cepa x81 y81 && equal_cepa x82 y82
    | C_eq (x71, x72), C_eq (y71, y72) ->
        equal_cepa x71 y71 && equal_cepa x72 y72
    | C_not x6, C_not y6 -> equal_cpa x6 y6
    | C_disj (x51, x52), C_disj (y51, y52) ->
        equal_cpa x51 y51 && equal_cpa x52 y52
    | C_conj_many x4, C_conj_many y4 -> Lista.equal_list (equal_cp ()) x4 y4
    | C_conj (x31, x32), C_conj (y31, y32) ->
        equal_cpa x31 y31 && equal_cpa x32 y32
    | C_false, C_false -> true
    | C_true, C_true -> true
and equal_cp () = ({HOL.equal = equal_cpa} : cp HOL.equal);;
let equal_cp = equal_cp ();;

let rec equal_bp () = ({HOL.equal = equal_bpa} : bp HOL.equal)
and equal_bpa
  x0 x1 = match x0, x1 with B_exception, B_finite_set x17 -> false
    | B_finite_set x17, B_exception -> false
    | B_string, B_finite_set x17 -> false
    | B_finite_set x17, B_string -> false
    | B_string, B_exception -> false
    | B_exception, B_string -> false
    | B_reg, B_finite_set x17 -> false
    | B_finite_set x17, B_reg -> false
    | B_reg, B_exception -> false
    | B_exception, B_reg -> false
    | B_reg, B_string -> false
    | B_string, B_reg -> false
    | B_undef, B_finite_set x17 -> false
    | B_finite_set x17, B_undef -> false
    | B_undef, B_exception -> false
    | B_exception, B_undef -> false
    | B_undef, B_string -> false
    | B_string, B_undef -> false
    | B_undef, B_reg -> false
    | B_reg, B_undef -> false
    | B_record x12, B_finite_set x17 -> false
    | B_finite_set x17, B_record x12 -> false
    | B_record x12, B_exception -> false
    | B_exception, B_record x12 -> false
    | B_record x12, B_string -> false
    | B_string, B_record x12 -> false
    | B_record x12, B_reg -> false
    | B_reg, B_record x12 -> false
    | B_record x12, B_undef -> false
    | B_undef, B_record x12 -> false
    | B_union (x111, x112), B_finite_set x17 -> false
    | B_finite_set x17, B_union (x111, x112) -> false
    | B_union (x111, x112), B_exception -> false
    | B_exception, B_union (x111, x112) -> false
    | B_union (x111, x112), B_string -> false
    | B_string, B_union (x111, x112) -> false
    | B_union (x111, x112), B_reg -> false
    | B_reg, B_union (x111, x112) -> false
    | B_union (x111, x112), B_undef -> false
    | B_undef, B_union (x111, x112) -> false
    | B_union (x111, x112), B_record x12 -> false
    | B_record x12, B_union (x111, x112) -> false
    | B_tuple x10, B_finite_set x17 -> false
    | B_finite_set x17, B_tuple x10 -> false
    | B_tuple x10, B_exception -> false
    | B_exception, B_tuple x10 -> false
    | B_tuple x10, B_string -> false
    | B_string, B_tuple x10 -> false
    | B_tuple x10, B_reg -> false
    | B_reg, B_tuple x10 -> false
    | B_tuple x10, B_undef -> false
    | B_undef, B_tuple x10 -> false
    | B_tuple x10, B_record x12 -> false
    | B_record x12, B_tuple x10 -> false
    | B_tuple x10, B_union (x111, x112) -> false
    | B_union (x111, x112), B_tuple x10 -> false
    | B_list x9, B_finite_set x17 -> false
    | B_finite_set x17, B_list x9 -> false
    | B_list x9, B_exception -> false
    | B_exception, B_list x9 -> false
    | B_list x9, B_string -> false
    | B_string, B_list x9 -> false
    | B_list x9, B_reg -> false
    | B_reg, B_list x9 -> false
    | B_list x9, B_undef -> false
    | B_undef, B_list x9 -> false
    | B_list x9, B_record x12 -> false
    | B_record x12, B_list x9 -> false
    | B_list x9, B_union (x111, x112) -> false
    | B_union (x111, x112), B_list x9 -> false
    | B_list x9, B_tuple x10 -> false
    | B_tuple x10, B_list x9 -> false
    | B_vec (x81, x82), B_finite_set x17 -> false
    | B_finite_set x17, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_exception -> false
    | B_exception, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_string -> false
    | B_string, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_reg -> false
    | B_reg, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_undef -> false
    | B_undef, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_record x12 -> false
    | B_record x12, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_union (x111, x112) -> false
    | B_union (x111, x112), B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_tuple x10 -> false
    | B_tuple x10, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_list x9 -> false
    | B_list x9, B_vec (x81, x82) -> false
    | B_real, B_finite_set x17 -> false
    | B_finite_set x17, B_real -> false
    | B_real, B_exception -> false
    | B_exception, B_real -> false
    | B_real, B_string -> false
    | B_string, B_real -> false
    | B_real, B_reg -> false
    | B_reg, B_real -> false
    | B_real, B_undef -> false
    | B_undef, B_real -> false
    | B_real, B_record x12 -> false
    | B_record x12, B_real -> false
    | B_real, B_union (x111, x112) -> false
    | B_union (x111, x112), B_real -> false
    | B_real, B_tuple x10 -> false
    | B_tuple x10, B_real -> false
    | B_real, B_list x9 -> false
    | B_list x9, B_real -> false
    | B_real, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_real -> false
    | B_unit, B_finite_set x17 -> false
    | B_finite_set x17, B_unit -> false
    | B_unit, B_exception -> false
    | B_exception, B_unit -> false
    | B_unit, B_string -> false
    | B_string, B_unit -> false
    | B_unit, B_reg -> false
    | B_reg, B_unit -> false
    | B_unit, B_undef -> false
    | B_undef, B_unit -> false
    | B_unit, B_record x12 -> false
    | B_record x12, B_unit -> false
    | B_unit, B_union (x111, x112) -> false
    | B_union (x111, x112), B_unit -> false
    | B_unit, B_tuple x10 -> false
    | B_tuple x10, B_unit -> false
    | B_unit, B_list x9 -> false
    | B_list x9, B_unit -> false
    | B_unit, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_unit -> false
    | B_unit, B_real -> false
    | B_real, B_unit -> false
    | B_bit, B_finite_set x17 -> false
    | B_finite_set x17, B_bit -> false
    | B_bit, B_exception -> false
    | B_exception, B_bit -> false
    | B_bit, B_string -> false
    | B_string, B_bit -> false
    | B_bit, B_reg -> false
    | B_reg, B_bit -> false
    | B_bit, B_undef -> false
    | B_undef, B_bit -> false
    | B_bit, B_record x12 -> false
    | B_record x12, B_bit -> false
    | B_bit, B_union (x111, x112) -> false
    | B_union (x111, x112), B_bit -> false
    | B_bit, B_tuple x10 -> false
    | B_tuple x10, B_bit -> false
    | B_bit, B_list x9 -> false
    | B_list x9, B_bit -> false
    | B_bit, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_bit -> false
    | B_bit, B_real -> false
    | B_real, B_bit -> false
    | B_bit, B_unit -> false
    | B_unit, B_bit -> false
    | B_bool, B_finite_set x17 -> false
    | B_finite_set x17, B_bool -> false
    | B_bool, B_exception -> false
    | B_exception, B_bool -> false
    | B_bool, B_string -> false
    | B_string, B_bool -> false
    | B_bool, B_reg -> false
    | B_reg, B_bool -> false
    | B_bool, B_undef -> false
    | B_undef, B_bool -> false
    | B_bool, B_record x12 -> false
    | B_record x12, B_bool -> false
    | B_bool, B_union (x111, x112) -> false
    | B_union (x111, x112), B_bool -> false
    | B_bool, B_tuple x10 -> false
    | B_tuple x10, B_bool -> false
    | B_bool, B_list x9 -> false
    | B_list x9, B_bool -> false
    | B_bool, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_bool -> false
    | B_bool, B_real -> false
    | B_real, B_bool -> false
    | B_bool, B_unit -> false
    | B_unit, B_bool -> false
    | B_bool, B_bit -> false
    | B_bit, B_bool -> false
    | B_int, B_finite_set x17 -> false
    | B_finite_set x17, B_int -> false
    | B_int, B_exception -> false
    | B_exception, B_int -> false
    | B_int, B_string -> false
    | B_string, B_int -> false
    | B_int, B_reg -> false
    | B_reg, B_int -> false
    | B_int, B_undef -> false
    | B_undef, B_int -> false
    | B_int, B_record x12 -> false
    | B_record x12, B_int -> false
    | B_int, B_union (x111, x112) -> false
    | B_union (x111, x112), B_int -> false
    | B_int, B_tuple x10 -> false
    | B_tuple x10, B_int -> false
    | B_int, B_list x9 -> false
    | B_list x9, B_int -> false
    | B_int, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_int -> false
    | B_int, B_real -> false
    | B_real, B_int -> false
    | B_int, B_unit -> false
    | B_unit, B_int -> false
    | B_int, B_bit -> false
    | B_bit, B_int -> false
    | B_int, B_bool -> false
    | B_bool, B_int -> false
    | B_tid x2, B_finite_set x17 -> false
    | B_finite_set x17, B_tid x2 -> false
    | B_tid x2, B_exception -> false
    | B_exception, B_tid x2 -> false
    | B_tid x2, B_string -> false
    | B_string, B_tid x2 -> false
    | B_tid x2, B_reg -> false
    | B_reg, B_tid x2 -> false
    | B_tid x2, B_undef -> false
    | B_undef, B_tid x2 -> false
    | B_tid x2, B_record x12 -> false
    | B_record x12, B_tid x2 -> false
    | B_tid x2, B_union (x111, x112) -> false
    | B_union (x111, x112), B_tid x2 -> false
    | B_tid x2, B_tuple x10 -> false
    | B_tuple x10, B_tid x2 -> false
    | B_tid x2, B_list x9 -> false
    | B_list x9, B_tid x2 -> false
    | B_tid x2, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_tid x2 -> false
    | B_tid x2, B_real -> false
    | B_real, B_tid x2 -> false
    | B_tid x2, B_unit -> false
    | B_unit, B_tid x2 -> false
    | B_tid x2, B_bit -> false
    | B_bit, B_tid x2 -> false
    | B_tid x2, B_bool -> false
    | B_bool, B_tid x2 -> false
    | B_tid x2, B_int -> false
    | B_int, B_tid x2 -> false
    | B_var x1, B_finite_set x17 -> false
    | B_finite_set x17, B_var x1 -> false
    | B_var x1, B_exception -> false
    | B_exception, B_var x1 -> false
    | B_var x1, B_string -> false
    | B_string, B_var x1 -> false
    | B_var x1, B_reg -> false
    | B_reg, B_var x1 -> false
    | B_var x1, B_undef -> false
    | B_undef, B_var x1 -> false
    | B_var x1, B_record x12 -> false
    | B_record x12, B_var x1 -> false
    | B_var x1, B_union (x111, x112) -> false
    | B_union (x111, x112), B_var x1 -> false
    | B_var x1, B_tuple x10 -> false
    | B_tuple x10, B_var x1 -> false
    | B_var x1, B_list x9 -> false
    | B_list x9, B_var x1 -> false
    | B_var x1, B_vec (x81, x82) -> false
    | B_vec (x81, x82), B_var x1 -> false
    | B_var x1, B_real -> false
    | B_real, B_var x1 -> false
    | B_var x1, B_unit -> false
    | B_unit, B_var x1 -> false
    | B_var x1, B_bit -> false
    | B_bit, B_var x1 -> false
    | B_var x1, B_bool -> false
    | B_bool, B_var x1 -> false
    | B_var x1, B_int -> false
    | B_int, B_var x1 -> false
    | B_var x1, B_tid x2 -> false
    | B_tid x2, B_var x1 -> false
    | B_finite_set x17, B_finite_set y17 ->
        Lista.equal_list Arith.equal_integer x17 y17
    | B_record x12, B_record y12 ->
        Lista.equal_list
          (Product_Type.equal_prod Stringa.equal_literal (equal_bp ())) x12 y12
    | B_union (x111, x112), B_union (y111, y112) ->
        ((x111 : string) = y111) &&
          Lista.equal_list
            (Product_Type.equal_prod Stringa.equal_literal (equal_tau ())) x112
            y112
    | B_tuple x10, B_tuple y10 -> Lista.equal_list (equal_bp ()) x10 y10
    | B_list x9, B_list y9 -> equal_bpa x9 y9
    | B_vec (x81, x82), B_vec (y81, y82) ->
        equal_order x81 y81 && equal_bpa x82 y82
    | B_tid x2, B_tid y2 -> ((x2 : string) = y2)
    | B_var x1, B_var y1 -> ((x1 : string) = y1)
    | B_exception, B_exception -> true
    | B_string, B_string -> true
    | B_reg, B_reg -> true
    | B_undef, B_undef -> true
    | B_real, B_real -> true
    | B_unit, B_unit -> true
    | B_bit, B_bit -> true
    | B_bool, B_bool -> true
    | B_int, B_int -> true
and equal_taua
  (T_refined_type (x1, x2, x3)) (T_refined_type (y1, y2, y3)) =
    equal_xpa x1 y1 && (equal_bpa x2 y2 && equal_cpa x3 y3)
and equal_tau () = ({HOL.equal = equal_taua} : tau HOL.equal);;
let equal_bp = equal_bp ();;
let equal_tau = equal_tau ();;

let equal_xp = ({HOL.equal = equal_xpa} : xp HOL.equal);;

let equal_lit = ({HOL.equal = equal_lita} : lit HOL.equal);;

type ap = A_monotype of tau | A_function of xp * bp * cp * tau;;

type bsub = BS_empty | BS_cons of bsub * bp * string;;

let rec subst_vp
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, V_lit lit -> V_lit lit
    | vp_5, zp5, V_var xp -> (if equal_xpa xp zp5 then vp_5 else V_var xp)
    | vp_5, zp5, V_vec vp_list -> V_vec (subst_vp_list_V_vec vp_5 zp5 vp_list)
    | vp_5, zp5, V_list vp_list ->
        V_list (subst_vp_list_V_list vp_5 zp5 vp_list)
    | vp_5, zp5, V_cons (vp1, vp2) ->
        V_cons (subst_vp vp_5 zp5 vp1, subst_vp vp_5 zp5 vp2)
    | vp_5, zp5, V_constr (ctor, vp) -> V_constr (ctor, subst_vp vp_5 zp5 vp)
    | vp_5, zp5, V_record field_vp_list ->
        V_record (subst_field_vp_list_V_record vp_5 zp5 field_vp_list)
    | vp_5, zp5, V_tuple vp_list ->
        V_tuple (subst_vp_list_V_tuple vp_5 zp5 vp_list)
    | vp_5, zp5, V_proj (p, vp) -> V_proj (p, subst_vp vp_5 zp5 vp)
and subst_vp_list_V_vec
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_vec vp_5 zp5 vp_list_XXX
and subst_vp_list_V_list
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_list vp_5 zp5 vp_list_XXX
and subst_vp_list_V_tuple
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_tuple vp_5 zp5 vp_list_XXX
and subst_field_vp_V_record
  vp_5 zp5 (field1, vp1) = (field1, subst_vp vp_5 zp5 vp1)
and subst_field_vp_list_V_record
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, field_vp_XXX :: field_vp_list_XXX ->
        subst_field_vp_V_record vp_5 zp5 field_vp_XXX ::
          subst_field_vp_list_V_record vp_5 zp5 field_vp_list_XXX;;

let rec subst_cep
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, CE_val vp -> CE_val (subst_vp vp5 zp5 vp)
    | vp5, zp5, CE_bop (bop, cep1, cep2) ->
        CE_bop (bop, subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, CE_many_plus cep_list ->
        CE_many_plus (subst_cep_list vp5 zp5 cep_list)
    | vp5, zp5, CE_uop (uop, cep) -> CE_uop (uop, subst_cep vp5 zp5 cep)
    | vp5, zp5, CE_proj (p, cep) -> CE_proj (p, subst_cep vp5 zp5 cep)
    | vp5, zp5, CE_field_access (xp, field) -> CE_field_access (xp, field)
and subst_cep_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, cep_XXX :: cep_list_XXX ->
        subst_cep vp5 zp5 cep_XXX :: subst_cep_list vp5 zp5 cep_list_XXX;;

let rec subst_cp
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, C_true -> C_true
    | vp5, zp5, C_false -> C_false
    | vp5, zp5, C_conj (cp1, cp2) ->
        C_conj (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
    | vp5, zp5, C_conj_many cp_list ->
        C_conj_many (subst_cp_list vp5 zp5 cp_list)
    | vp5, zp5, C_disj (cp1, cp2) ->
        C_disj (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
    | vp5, zp5, C_not cp -> C_not (subst_cp vp5 zp5 cp)
    | vp5, zp5, C_eq (cep1, cep2) ->
        C_eq (subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, C_leq (cep1, cep2) ->
        C_leq (subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, C_imp (cp1, cp2) ->
        C_imp (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
and subst_cp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, cp_XXX :: cp_list_XXX ->
        subst_cp vp5 zp5 cp_XXX :: subst_cp_list vp5 zp5 cp_list_XXX;;

let rec tsubst_bp
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with
    bp_5, tvar5, B_var tvar ->
      (if ((tvar : string) = tvar5) then bp_5 else B_var tvar)
    | bp_5, tvar5, B_tid id -> B_tid id
    | bp_5, tvar5, B_int -> B_int
    | bp_5, tvar5, B_bool -> B_bool
    | bp_5, tvar5, B_bit -> B_bit
    | bp_5, tvar5, B_unit -> B_unit
    | bp_5, tvar5, B_real -> B_real
    | bp_5, tvar5, B_vec (order, bp) -> B_vec (order, tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, B_list bp -> B_list (tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, B_tuple bp_list ->
        B_tuple (tsubst_bp_list bp_5 tvar5 bp_list)
    | bp_5, tvar5, B_union (id, ctor_tau_list) ->
        B_union (id, tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list)
    | bp_5, tvar5, B_record field_bp_list ->
        B_record (tsubst_field_bp_list bp_5 tvar5 field_bp_list)
    | bp_5, tvar5, B_undef -> B_undef
    | bp_5, tvar5, B_reg -> B_reg
    | bp_5, tvar5, B_string -> B_string
    | bp_5, tvar5, B_exception -> B_exception
    | bp_5, tvar5, B_finite_set num_list -> B_finite_set num_list
and tsubst_tp
  bp5 tvar5 (T_refined_type (zp, bp, cp)) =
    T_refined_type (zp, tsubst_bp bp5 tvar5 bp, cp)
and tsubst_ctor_tau bp_5 tvar5 (ctor1, tp1) = (ctor1, tsubst_tp bp_5 tvar5 tp1)
and tsubst_ctor_tau_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, ctor_tau_XXX :: ctor_tau_list_XXX ->
        tsubst_ctor_tau bp_5 tvar5 ctor_tau_XXX ::
          tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list_XXX
and tsubst_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, bp_XXX :: bp_list_XXX ->
        tsubst_bp bp_5 tvar5 bp_XXX :: tsubst_bp_list bp_5 tvar5 bp_list_XXX
and tsubst_field_bp
  bp_5 tvar5 (field1, bp1) = (field1, tsubst_bp bp_5 tvar5 bp1)
and tsubst_field_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, field_bp_XXX :: field_bp_list_XXX ->
        tsubst_field_bp bp_5 tvar5 field_bp_XXX ::
          tsubst_field_bp_list bp_5 tvar5 field_bp_list_XXX;;

end;; (*struct SyntaxVCT*)

module Utils : sig
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val string_of_digit : Arith.nat -> Stringa.char list
  val string_of_nat : Arith.nat -> Stringa.char list
  val string_of_int : Arith.int -> Stringa.char list
  val string_lit_map : string -> ('a -> string) -> 'a list -> string
  val string_lit_of_int : Arith.int -> string
  val string_lit_of_nat : Arith.nat -> string
  val string_of_literal : string -> Stringa.char list
  val string_to_literal : Stringa.char list -> string
  val string_lit_of_integer : Z.t -> string
end = struct

let rec unzip
  = function [] -> ([], [])
    | (x, y) :: xy -> (let (xs, ys) = unzip xy in (x :: xs, y :: ys));;

let rec string_of_digit
  n = (if Arith.equal_nat n Arith.zero_nat
        then [Stringa.Chara
                (false, false, false, false, true, true, false, false)]
        else (if Arith.equal_nat n Arith.one_nat
               then [Stringa.Chara
                       (true, false, false, false, true, true, false, false)]
               else (if Arith.equal_nat n (Arith.nat_of_integer (Z.of_int 2))
                      then [Stringa.Chara
                              (false, true, false, false, true, true, false,
                                false)]
                      else (if Arith.equal_nat n
                                 (Arith.nat_of_integer (Z.of_int 3))
                             then [Stringa.Chara
                                     (true, true, false, false, true, true,
                                       false, false)]
                             else (if Arith.equal_nat n
(Arith.nat_of_integer (Z.of_int 4))
                                    then [Stringa.Chara
    (false, false, true, false, true, true, false, false)]
                                    else (if Arith.equal_nat n
       (Arith.nat_of_integer (Z.of_int 5))
   then [Stringa.Chara (true, false, true, false, true, true, false, false)]
   else (if Arith.equal_nat n (Arith.nat_of_integer (Z.of_int 6))
          then [Stringa.Chara
                  (false, true, true, false, true, true, false, false)]
          else (if Arith.equal_nat n (Arith.nat_of_integer (Z.of_int 7))
                 then [Stringa.Chara
                         (true, true, true, false, true, true, false, false)]
                 else (if Arith.equal_nat n (Arith.nat_of_integer (Z.of_int 8))
                        then [Stringa.Chara
                                (false, false, false, true, true, true, false,
                                  false)]
                        else [Stringa.Chara
                                (true, false, false, true, true, true, false,
                                  false)])))))))));;

let rec string_of_nat
  n = (if Arith.less_nat n (Arith.nat_of_integer (Z.of_int 10))
        then string_of_digit n
        else string_of_nat
               (Arith.divide_nat n (Arith.nat_of_integer (Z.of_int 10))) @
               string_of_digit
                 (Arith.modulo_nat n (Arith.nat_of_integer (Z.of_int 10))));;

let rec string_of_int
  i = (if Arith.less_int i Arith.zero_int
        then [Stringa.Chara
                (true, false, true, true, false, true, false, false)] @
               string_of_nat (Arith.nat (Arith.uminus_int i))
        else string_of_nat (Arith.nat i));;

let rec string_lit_map
  delim f x2 = match delim, f, x2 with delim, f, [] -> ""
    | delim, f, [x] -> f x
    | delim, f, x :: v :: va ->
        (f x ^ delim) ^ string_lit_map delim f (v :: va);;

let rec string_lit_of_int x = Fun.comp Stringa.implode string_of_int x;;

let rec string_lit_of_nat x = Fun.comp Stringa.implode string_of_nat x;;

let rec string_of_literal s = Stringa.explode s;;

let rec string_to_literal s = Stringa.implode s;;

let rec string_lit_of_integer
  x = Fun.comp string_lit_of_int (fun a -> Arith.Int_of_integer a) x;;

end;; (*struct Utils*)

module Contexts : sig
  type g_entry = GEPair of SyntaxVCT.bp * SyntaxVCT.cp | GETyp of SyntaxVCT.tau
  type ('a, 'b) gamma_ext =
    Gamma_ext of
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap *
        (SyntaxVCT.xp * g_entry) list * (SyntaxVCT.xp * g_entry) list *
        (SyntaxVCT.xp * SyntaxVCT.tau) list *
        (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap *
        (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.xp list *
        SyntaxVCT.order option * SyntaxVCT.tau option * 'b
  val b_of : SyntaxVCT.tau -> SyntaxVCT.bp
  val c_of : SyntaxVCT.tau -> SyntaxVCT.cp
  val conj : SyntaxVCT.cp list -> SyntaxVCT.cp
  val mapi : (Arith.nat -> 'a -> 'b) -> 'a list -> 'b list
  val gamma_x : ('a, 'b) gamma_ext -> (SyntaxVCT.xp * g_entry) list
  val x_of : SyntaxVCT.xp -> string
  val pp_G : ('a, unit) gamma_ext -> string
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val lookup : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
  val update : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list
  val gamma_x_update :
    ((SyntaxVCT.xp * g_entry) list -> (SyntaxVCT.xp * g_entry) list) ->
      ('a, 'b) gamma_ext -> ('a, 'b) gamma_ext
  val add_var :
    ('a, unit) gamma_ext -> SyntaxVCT.xp * g_entry -> ('a, unit) gamma_ext
  val unify_b_aux :
    SyntaxVCT.bp -> SyntaxVCT.bp -> ((string * SyntaxVCT.bp) list) option
  val unify_b :
    SyntaxVCT.bp -> SyntaxVCT.bp -> ((string * SyntaxVCT.bp) list) option
  val add_vars :
    ('a, unit) gamma_ext ->
      (SyntaxVCT.xp * g_entry) list -> ('a, unit) gamma_ext
  val emptyEnv : ('a, unit) gamma_ext
  val mk_l_eq_c : SyntaxVCT.xp -> SyntaxVCT.lit -> SyntaxVCT.cp
  val literal_type : SyntaxVCT.lit -> SyntaxVCT.bp
  val mk_l_eq_t : SyntaxVCT.lit -> SyntaxVCT.tau
  val mk_list_c : SyntaxVCT.xp -> SyntaxVCT.xp list -> SyntaxVCT.cp
  val mk_v_eq_c : SyntaxVCT.xp -> SyntaxVCT.vp -> SyntaxVCT.cp
  val mk_v_eq_t : SyntaxVCT.bp -> SyntaxVCT.vp -> SyntaxVCT.tau
  val subst_c_x : SyntaxVCT.cp -> SyntaxVCT.xp -> SyntaxVCT.cp
  val convert_ge :
    (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
      (SyntaxVCT.xp * g_entry) list
  val mk_proj_eq : SyntaxVCT.xp -> string -> SyntaxVCT.cp
  val subst_c_v0 : SyntaxVCT.cp -> SyntaxVCT.vp -> SyntaxVCT.cp
  val tuple_proj : Arith.nat -> Arith.nat -> SyntaxVCT.vp -> SyntaxVCT.vp
  val add_vars_ge :
    ('a, unit) gamma_ext ->
      (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
        ('a, unit) gamma_ext
  val lookup_ivar : ('a, unit) gamma_ext -> SyntaxVCT.xp -> g_entry option
  val remove_tick : string -> string
  val gamma_s_update :
    (SyntaxVCT.xp list -> SyntaxVCT.xp list) ->
      ('a, 'b) gamma_ext -> ('a, 'b) gamma_ext
  val gamma_s : ('a, 'b) gamma_ext -> SyntaxVCT.xp list
  val add_to_scope :
    ('a, unit) gamma_ext -> SyntaxVCT.xp list -> ('a, unit) gamma_ext
  val lookup_scope : ('a, unit) gamma_ext -> SyntaxVCT.xp -> bool
  val mk_proj_eq_x : SyntaxVCT.xp -> SyntaxVCT.xp -> string -> SyntaxVCT.cp
  val convert_to_bc :
    Arith.nat -> Arith.nat -> SyntaxVCT.tau -> SyntaxVCT.bp * SyntaxVCT.cp
  val convert_to_st : SyntaxVCT.tau list -> SyntaxVCT.bp list * SyntaxVCT.cp
  val tsubst_b_list :
    SyntaxVCT.bp -> (string * SyntaxVCT.bp) list -> SyntaxVCT.bp
  val mk_x_eq_c_tuple : SyntaxVCT.xp -> SyntaxVCT.xp list -> SyntaxVCT.cp
  val gamma_f :
    ('a, 'b) gamma_ext ->
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap
  val gamma_u : ('a, 'b) gamma_ext -> (SyntaxVCT.xp * g_entry) list
end = struct

type g_entry = GEPair of SyntaxVCT.bp * SyntaxVCT.cp | GETyp of SyntaxVCT.tau;;

type ('a, 'b) gamma_ext =
  Gamma_ext of
    (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
      Finite_Map.fmap *
      (SyntaxVCT.xp * g_entry) list * (SyntaxVCT.xp * g_entry) list *
      (SyntaxVCT.xp * SyntaxVCT.tau) list *
      (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap *
      (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.xp list *
      SyntaxVCT.order option * SyntaxVCT.tau option * 'b;;

let rec b_of (SyntaxVCT.T_refined_type (uu, b, uv)) = b;;

let rec c_of (SyntaxVCT.T_refined_type (uu, uv, c)) = c;;

let rec conj
  xs = Lista.foldr
         (fun x y ->
           (if SyntaxVCT.equal_cpa x SyntaxVCT.C_true then y
             else (if SyntaxVCT.equal_cpa y SyntaxVCT.C_true then x
                    else SyntaxVCT.C_conj (x, y))))
         xs SyntaxVCT.C_true;;

let rec mapi
  f xs =
    Lista.map (fun (a, b) -> f a b)
      (Lista.zip (Lista.upt Arith.zero_nat (Lista.size_list xs)) xs);;

let rec gamma_x
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
      gamma_e, more))
    = gamma_x;;

let rec x_of (SyntaxVCT.VNamed x) = x;;

let rec pp_G
  g = Stringa.implode
        (Lista.maps (fun (x, _) -> Stringa.explode (x_of x ^ " "))
          (gamma_x g));;

let rec unzip
  = function [] -> ([], [])
    | (x, y) :: xys -> (let (xs, ys) = unzip xys in (x :: xs, y :: ys));;

let rec lookup _A
  xa0 x = match xa0, x with
    (xa, a) :: gs, x -> (if HOL.eq _A x xa then Some a else lookup _A gs x)
    | [], uu -> None;;

let rec update _A
  xa0 x v = match xa0, x, v with
    (xa, a) :: gs, x, v ->
      (if HOL.eq _A x xa then (x, v) :: gs else (xa, a) :: update _A gs x v)
    | [], x, v -> [(x, v)];;

let rec gamma_x_update
  gamma_xa
    (Gamma_ext
      (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
        gamma_e, more))
    = Gamma_ext
        (gamma_f, gamma_xa gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s,
          gamma_d, gamma_e, more);;

let rec add_var
  gamma (x, t) = gamma_x_update (fun _ -> (x, t) :: gamma_x gamma) gamma;;

let rec unify_b_aux
  b x1 = match b, x1 with b, SyntaxVCT.B_var x -> Some [(x, b)]
    | uu, SyntaxVCT.B_tid v -> None
    | uu, SyntaxVCT.B_int -> None
    | uu, SyntaxVCT.B_bool -> None
    | uu, SyntaxVCT.B_bit -> None
    | uu, SyntaxVCT.B_unit -> None
    | uu, SyntaxVCT.B_real -> None
    | uu, SyntaxVCT.B_vec (v, va) -> None
    | uu, SyntaxVCT.B_list v -> None
    | uu, SyntaxVCT.B_tuple v -> None
    | uu, SyntaxVCT.B_union (v, va) -> None
    | uu, SyntaxVCT.B_record v -> None
    | uu, SyntaxVCT.B_undef -> None
    | uu, SyntaxVCT.B_reg -> None
    | uu, SyntaxVCT.B_string -> None
    | uu, SyntaxVCT.B_exception -> None
    | uu, SyntaxVCT.B_finite_set v -> None;;

let rec unify_b
  b1 b2 = match b1, b2 with
    SyntaxVCT.B_vec (o1, b1), SyntaxVCT.B_vec (o2, b2) ->
      (if SyntaxVCT.equal_order o1 o2
        then (match unify_b b1 b2 with None -> None | Some a -> Some a)
        else None)
    | SyntaxVCT.B_list b1, SyntaxVCT.B_list b2 ->
        (match unify_b b1 b2 with None -> None | Some a -> Some a)
    | SyntaxVCT.B_var v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_var v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_var v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_var v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tid v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tid v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_tid v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_tid v)
                 | Some a -> Some a))
    | SyntaxVCT.B_int, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_int b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_int b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_int
                 | Some a -> Some a))
    | SyntaxVCT.B_bool, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_bool b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_bool b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_bool
                 | Some a -> Some a))
    | SyntaxVCT.B_bit, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_bit b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_bit b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_bit
                 | Some a -> Some a))
    | SyntaxVCT.B_unit, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_unit b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_unit b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_unit
                 | Some a -> Some a))
    | SyntaxVCT.B_real, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_real b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_real b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_real
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_var va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_var va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_var va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_var va) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_tid va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_tid va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_tid va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tid va) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_int ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_int
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_int
                 with None -> unify_b_aux SyntaxVCT.B_int (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_bool ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_bool
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_bool
                 with None -> unify_b_aux SyntaxVCT.B_bool (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_bit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_bit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_bit
                 with None -> unify_b_aux SyntaxVCT.B_bit (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_unit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_unit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_unit
                 with None -> unify_b_aux SyntaxVCT.B_unit (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_real ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_real
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_real
                 with None -> unify_b_aux SyntaxVCT.B_real (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_vec (va, vb) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_vec (va, vb))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_vec (va, vb))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_tuple va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_tuple va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_tuple va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tuple va) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_union (va, vb) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v)
              (SyntaxVCT.B_union (va, vb))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_union (va, vb))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_union (va, vb)) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_record va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_record va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_record va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_record va) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_undef ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_undef
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_undef
                 with None -> unify_b_aux SyntaxVCT.B_undef (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_reg ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_reg
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_reg
                 with None -> unify_b_aux SyntaxVCT.B_reg (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_string ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_string
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_string
                 with None ->
                   unify_b_aux SyntaxVCT.B_string (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_exception ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) SyntaxVCT.B_exception
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) SyntaxVCT.B_exception
                 with None ->
                   unify_b_aux SyntaxVCT.B_exception (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_list v, SyntaxVCT.B_finite_set va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_finite_set va)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_finite_set va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_finite_set va) (SyntaxVCT.B_list v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_record v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_record v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_record v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_record v)
                 | Some a -> Some a))
    | SyntaxVCT.B_undef, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_undef b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_undef b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_undef
                 | Some a -> Some a))
    | SyntaxVCT.B_reg, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_reg b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_reg b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_reg
                 | Some a -> Some a))
    | SyntaxVCT.B_string, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_string b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_string b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_string
                 | Some a -> Some a))
    | SyntaxVCT.B_exception, b2 ->
        (if SyntaxVCT.equal_bpa SyntaxVCT.B_exception b2 then Some []
          else (match unify_b_aux SyntaxVCT.B_exception b2
                 with None -> unify_b_aux b2 SyntaxVCT.B_exception
                 | Some a -> Some a))
    | SyntaxVCT.B_finite_set v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_finite_set v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_finite_set v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_finite_set v)
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_var v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_var v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_var v)
                 with None -> unify_b_aux (SyntaxVCT.B_var v) b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_tid v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_tid v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_tid v)
                 with None -> unify_b_aux (SyntaxVCT.B_tid v) b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_int ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_int then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_int
                 with None -> unify_b_aux SyntaxVCT.B_int b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_bool ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_bool then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_bool
                 with None -> unify_b_aux SyntaxVCT.B_bool b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_bit ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_bit then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_bit
                 with None -> unify_b_aux SyntaxVCT.B_bit b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_unit ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_unit then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_unit
                 with None -> unify_b_aux SyntaxVCT.B_unit b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_real ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_real then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_real
                 with None -> unify_b_aux SyntaxVCT.B_real b1
                 | Some a -> Some a))
    | SyntaxVCT.B_vec (va, vb), SyntaxVCT.B_list v ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_list v)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_list v)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_vec (va, vb))
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_tuple v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_tuple v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_tuple v)
                 with None -> unify_b_aux (SyntaxVCT.B_tuple v) b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_union (v, va) ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_union (v, va)) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_union (v, va))
                 with None -> unify_b_aux (SyntaxVCT.B_union (v, va)) b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_record v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_record v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_record v)
                 with None -> unify_b_aux (SyntaxVCT.B_record v) b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_undef ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_undef then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_undef
                 with None -> unify_b_aux SyntaxVCT.B_undef b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_reg ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_reg then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_reg
                 with None -> unify_b_aux SyntaxVCT.B_reg b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_string ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_string then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_string
                 with None -> unify_b_aux SyntaxVCT.B_string b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_exception ->
        (if SyntaxVCT.equal_bpa b1 SyntaxVCT.B_exception then Some []
          else (match unify_b_aux b1 SyntaxVCT.B_exception
                 with None -> unify_b_aux SyntaxVCT.B_exception b1
                 | Some a -> Some a))
    | b1, SyntaxVCT.B_finite_set v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_finite_set v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_finite_set v)
                 with None -> unify_b_aux (SyntaxVCT.B_finite_set v) b1
                 | Some a -> Some a));;

let rec add_vars gamma bs = gamma_x_update (fun _ -> bs @ gamma_x gamma) gamma;;

let emptyEnv : ('a, unit) gamma_ext
  = Gamma_ext
      (Finite_Map.fmempty, [], [], [], Finite_Map.fmempty, Finite_Map.fmempty,
        [], None, None, ());;

let rec mk_l_eq_c
  x l = SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit l));;

let rec literal_type = function SyntaxVCT.L_true -> SyntaxVCT.B_bool
                       | SyntaxVCT.L_false -> SyntaxVCT.B_bool
                       | SyntaxVCT.L_num n -> SyntaxVCT.B_int
                       | SyntaxVCT.L_zero -> SyntaxVCT.B_bit
                       | SyntaxVCT.L_one -> SyntaxVCT.B_bit
                       | SyntaxVCT.L_unit -> SyntaxVCT.B_unit
                       | SyntaxVCT.L_string uu -> SyntaxVCT.B_string
                       | SyntaxVCT.L_real uv -> SyntaxVCT.B_real
                       | SyntaxVCT.L_undef -> SyntaxVCT.B_undef;;

let rec mk_l_eq_t
  l = SyntaxVCT.T_refined_type
        (SyntaxVCT.VIndex, literal_type l, mk_l_eq_c SyntaxVCT.VIndex l);;

let rec mk_list_c
  x xs =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_list (Lista.map (fun a -> SyntaxVCT.V_var a) xs)));;

let rec mk_v_eq_c
  x v = SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x), SyntaxVCT.CE_val v);;

let rec mk_v_eq_t
  b v = SyntaxVCT.T_refined_type
          (SyntaxVCT.VIndex, b,
            SyntaxVCT.C_eq
              (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
                SyntaxVCT.CE_val v));;

let rec subst_c_x
  c x = SyntaxVCT.subst_cp (SyntaxVCT.V_var x) SyntaxVCT.VIndex c;;

let rec convert_ge xs = Lista.map (fun (x, (b, c)) -> (x, GEPair (b, c))) xs;;

let rec mk_proj_eq
  x field =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
        SyntaxVCT.CE_val (SyntaxVCT.V_proj (field, SyntaxVCT.V_var x)));;

let rec subst_c_v0 c v = SyntaxVCT.subst_cp v SyntaxVCT.VIndex c;;

let rec tuple_proj
  i n v =
    SyntaxVCT.V_proj
      (Stringa.implode
         (Utils.string_of_nat n @
           [Stringa.Chara
              (false, false, false, true, true, false, true, false)] @
             Utils.string_of_nat i),
        v);;

let rec add_vars_ge
  g xs = add_vars g (Lista.map (fun (x, (b, c)) -> (x, GEPair (b, c))) xs);;

let rec lookup_ivar gamma x = lookup SyntaxVCT.equal_xp (gamma_x gamma) x;;

let rec remove_tick
  y = (match Stringa.explode y with [] -> y
        | x :: xs ->
          (if Stringa.equal_char x
                (Stringa.Chara
                  (true, true, true, false, false, true, false, false))
            then Stringa.implode xs else y));;

let rec gamma_s_update
  gamma_sa
    (Gamma_ext
      (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
        gamma_e, more))
    = Gamma_ext
        (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_sa gamma_s,
          gamma_d, gamma_e, more);;

let rec gamma_s
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
      gamma_e, more))
    = gamma_s;;

let rec add_to_scope
  gamma xs = gamma_s_update (fun _ -> xs @ gamma_s gamma) gamma;;

let rec lookup_scope
  gamma x = Lista.member SyntaxVCT.equal_xp (gamma_s gamma) x;;

let rec mk_proj_eq_x
  x y field =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var y),
        SyntaxVCT.CE_val (SyntaxVCT.V_proj (field, SyntaxVCT.V_var x)));;

let rec convert_to_bc
  n i (SyntaxVCT.T_refined_type (z, b, c)) =
    (b, subst_c_v0 c (tuple_proj i n (SyntaxVCT.V_var SyntaxVCT.VIndex)));;

let rec convert_to_st
  ts = (let (blist, clist) =
          unzip (Lista.map
                  (fun (a, b) -> convert_to_bc (Lista.size_list ts) a b)
                  (Lista.enumerate Arith.one_nat ts))
          in
         (blist, conj clist));;

let rec tsubst_b_list
  b x1 = match b, x1 with b, [] -> b
    | ba, (x, b) :: xvs -> tsubst_b_list (SyntaxVCT.tsubst_bp b x ba) xvs;;

let rec mk_x_eq_c_tuple
  x xs =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_tuple (Lista.map (fun a -> SyntaxVCT.V_var a) xs)));;

let rec gamma_f
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
      gamma_e, more))
    = gamma_f;;

let rec gamma_u
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_d,
      gamma_e, more))
    = gamma_u;;

end;; (*struct Contexts*)

module ContextsPiDelta : sig
  type ('a, 'b) phi_ext =
    Phi_ext of
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap *
        (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap * 'b
  type 'a delta_ext = Delta_ext of (string * SyntaxVCT.tau) list * 'a
  type 'a theta_ext =
    Theta_ext of
      (SyntaxVCT.xp * SyntaxVCT.tau) list * SyntaxVCT.order option * 'a
  val phi_f_update :
    ((SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
       Finite_Map.fmap ->
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap) ->
      ('a, 'b) phi_ext -> ('a, 'b) phi_ext
  val phi_f :
    ('a, 'b) phi_ext ->
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap
  val add_fun :
    ('a, unit) phi_ext ->
      SyntaxVCT.xp * (SyntaxVCT.ap * 'a option) -> ('a, unit) phi_ext
  val theta_T_update :
    ((SyntaxVCT.xp * SyntaxVCT.tau) list ->
      (SyntaxVCT.xp * SyntaxVCT.tau) list) ->
      'a theta_ext -> 'a theta_ext
  val theta_T : 'a theta_ext -> (SyntaxVCT.xp * SyntaxVCT.tau) list
  val add_to_scope_theta : unit theta_ext -> SyntaxVCT.xp list -> unit theta_ext
  val add_type :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau -> unit theta_ext
  val emptyDEnv : unit delta_ext
  val emptyPiEnv : ('a, unit) phi_ext
  val delta_m : 'a delta_ext -> (string * SyntaxVCT.tau) list
  val lookup_mvar : unit delta_ext -> string -> SyntaxVCT.tau option
  val update_type :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau -> unit theta_ext
  val emptyThetaEnv : unit theta_ext
  val phi_o :
    ('a, 'b) phi_ext -> (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap
  val lookup_fun_aux :
    ('a, unit) phi_ext ->
      SyntaxVCT.xp -> ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list) option
  val lookup_constr_in_type : SyntaxVCT.tau -> string -> SyntaxVCT.tau option
  val lookup_constr_aux :
    (SyntaxVCT.xp * SyntaxVCT.tau) list -> string -> SyntaxVCT.tau option
  val lookup_field_in_type : SyntaxVCT.tau -> string -> SyntaxVCT.bp option
  val lookup_field_record_aux :
    (SyntaxVCT.xp * SyntaxVCT.tau) list ->
      string -> (SyntaxVCT.xp * SyntaxVCT.tau) option
  val lookup_field_record :
    unit theta_ext -> string -> (SyntaxVCT.xp * SyntaxVCT.tau) option
  val lookup_record_name : unit theta_ext -> string -> string option
  val lookup_constr_union : unit theta_ext -> string -> SyntaxVCT.tau option
  val lookup_constr_union_x :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau option
  val lookup_constr_union_type :
    unit theta_ext -> string -> (SyntaxVCT.tau * SyntaxVCT.tau) option
  val theta_d : 'a theta_ext -> SyntaxVCT.order option
  val phi_o_update :
    ((SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap ->
      (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap) ->
      ('a, 'b) phi_ext -> ('a, 'b) phi_ext
  val theta_d_update :
    (SyntaxVCT.order option -> SyntaxVCT.order option) ->
      'a theta_ext -> 'a theta_ext
end = struct

type ('a, 'b) phi_ext =
  Phi_ext of
    (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
      Finite_Map.fmap *
      (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap * 'b;;

type 'a delta_ext = Delta_ext of (string * SyntaxVCT.tau) list * 'a;;

type 'a theta_ext =
  Theta_ext of
    (SyntaxVCT.xp * SyntaxVCT.tau) list * SyntaxVCT.order option * 'a;;

let rec phi_f_update
  phi_fa (Phi_ext (phi_f, phi_o, more)) = Phi_ext (phi_fa phi_f, phi_o, more);;

let rec phi_f (Phi_ext (phi_f, phi_o, more)) = phi_f;;

let rec add_fun
  phi (x, (f, s)) =
    (match Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_f phi) x
      with None ->
        phi_f_update
          (fun _ ->
            Finite_Map.fmupd SyntaxVCT.equal_xp x [(x, (f, s))] (phi_f phi))
          phi
      | Some fs ->
        phi_f_update
          (fun _ ->
            Finite_Map.fmupd SyntaxVCT.equal_xp x ((x, (f, s)) :: fs)
              (phi_f phi))
          phi);;

let rec theta_T_update
  theta_Ta (Theta_ext (theta_T, theta_d, more)) =
    Theta_ext (theta_Ta theta_T, theta_d, more);;

let rec theta_T (Theta_ext (theta_T, theta_d, more)) = theta_T;;

let rec add_to_scope_theta theta xs = theta;;

let rec add_type
  phi x xa2 = match phi, x, xa2 with
    phi, x,
      SyntaxVCT.T_refined_type (zvar, SyntaxVCT.B_union (uname, variants), c)
      -> add_to_scope_theta
           (theta_T_update
             (fun _ ->
               (x, SyntaxVCT.T_refined_type
                     (zvar, SyntaxVCT.B_union (uname, variants), c)) ::
                 theta_T phi)
             phi)
           (Lista.map (fun s -> SyntaxVCT.VNamed (Product_Type.fst s)) variants)
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb)) ::
              theta_T phi)
          phi
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb)) ::
              theta_T phi)
          phi;;

let emptyDEnv : unit delta_ext = Delta_ext ([], ());;

let emptyPiEnv : ('a, unit) phi_ext
  = Phi_ext (Finite_Map.fmempty, Finite_Map.fmempty, ());;

let rec delta_m (Delta_ext (delta_m, more)) = delta_m;;

let rec lookup_mvar
  delta x = Contexts.lookup Stringa.equal_literal (delta_m delta) x;;

let rec update_type
  theta x t =
    theta_T_update
      (fun _ -> Contexts.update SyntaxVCT.equal_xp (theta_T theta) x t) theta;;

let emptyThetaEnv : unit theta_ext = Theta_ext ([], None, ());;

let rec phi_o (Phi_ext (phi_f, phi_o, more)) = phi_o;;

let rec lookup_fun_aux
  phi x =
    (match Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_o phi) x
      with None -> Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_f phi) x
      | Some xs ->
        Some (Lista.concat
               (Lista.map_filter
                 (Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_f phi)) xs)));;

let rec lookup_constr_in_type
  xa0 x = match xa0, x with
    SyntaxVCT.T_refined_type (uu, SyntaxVCT.B_union (s, fs), c), x ->
      Contexts.lookup Stringa.equal_literal fs x
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb), uw -> None;;

let rec lookup_constr_aux
  x0 uu = match x0, uu with [], uu -> None
    | (xa, t) :: ts, x ->
        (match lookup_constr_in_type t x with None -> lookup_constr_aux ts x
          | Some _ -> Some t);;

let rec lookup_field_in_type
  xa0 x = match xa0, x with
    SyntaxVCT.T_refined_type (uu, SyntaxVCT.B_record fs, c), x ->
      Contexts.lookup Stringa.equal_literal fs x
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_union (vc, vd), vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb), uw -> None;;

let rec lookup_field_record_aux
  x0 uu = match x0, uu with [], uu -> None
    | (xa, t) :: ts, x ->
        (match lookup_field_in_type t x
          with None -> lookup_field_record_aux ts x | Some _ -> Some (xa, t));;

let rec lookup_field_record
  theta fid = lookup_field_record_aux (theta_T theta) fid;;

let rec lookup_record_name
  theta fid =
    (match lookup_field_record theta fid with None -> None
      | Some a ->
        (match a with (SyntaxVCT.VNamed aa, _) -> Some aa
          | (SyntaxVCT.VIndex, _) -> None));;

let rec lookup_constr_union theta fid = lookup_constr_aux (theta_T theta) fid;;

let rec lookup_constr_union_x g (SyntaxVCT.VNamed x) = lookup_constr_union g x;;

let rec lookup_constr_union_type
  phi fid =
    (match lookup_constr_union phi fid with None -> None
      | Some t1 ->
        (match lookup_constr_in_type t1 fid with None -> None
          | Some t2 -> Some (t1, t2)));;

let rec theta_d (Theta_ext (theta_T, theta_d, more)) = theta_d;;

let rec phi_o_update
  phi_oa (Phi_ext (phi_f, phi_o, more)) = Phi_ext (phi_f, phi_oa phi_o, more);;

let rec theta_d_update
  theta_da (Theta_ext (theta_T, theta_d, more)) =
    Theta_ext (theta_T, theta_da theta_d, more);;

end;; (*struct ContextsPiDelta*)

module Location : sig
  type 'a pos_ext = Pos_ext of string * Z.t * Z.t * Z.t * 'a
  type loc = Loc_unknown | Loc_range of unit pos_ext * unit pos_ext
end = struct

type 'a pos_ext = Pos_ext of string * Z.t * Z.t * Z.t * 'a;;

type loc = Loc_unknown | Loc_range of unit pos_ext * unit pos_ext;;

end;; (*struct Location*)

module SyntaxPED : sig
  type patp = Pp_id of Location.loc * string | Pp_wild of Location.loc |
    Pp_lit of Location.loc * SyntaxVCT.lit |
    Pp_typ of Location.loc * SyntaxVCT.tau * patp |
    Pp_app of Location.loc * string * patp list |
    Pp_tup of Location.loc * patp list |
    Pp_vector_concat of Location.loc * patp list |
    Pp_as_var of Location.loc * patp * SyntaxVCT.xp |
    Pp_as_typ of Location.loc * patp * SyntaxVCT.tau |
    Pp_cons of Location.loc * patp * patp |
    Pp_string_append of Location.loc * patp list |
    Pp_vector of Location.loc * patp list | Pp_list of Location.loc * patp list
    | Pp_record of Location.loc * (string * patp) list
  type lexpp = LEXPp_mvar of Location.loc * string |
    LEXPp_cast of Location.loc * SyntaxVCT.tau * string |
    LEXPp_tup of Location.loc * lexpp list |
    LEXPp_field of Location.loc * lexpp * string
  type loop = While | Until
  type ep = Ep_val of Location.loc * SyntaxVCT.vp |
    Ep_mvar of Location.loc * string | Ep_concat of Location.loc * ep list |
    Ep_tuple of Location.loc * ep list |
    Ep_app of Location.loc * SyntaxVCT.xp * ep |
    Ep_bop of Location.loc * SyntaxVCT.bop * ep * ep |
    Ep_uop of Location.loc * SyntaxVCT.uop * ep |
    Ep_proj of Location.loc * string * ep |
    Ep_constr of Location.loc * string * ep |
    Ep_field_access of Location.loc * ep * string |
    Ep_sizeof of Location.loc * SyntaxVCT.cep |
    Ep_cast of Location.loc * SyntaxVCT.tau * ep |
    Ep_record of Location.loc * (string * ep) list |
    Ep_record_update of Location.loc * ep * (string * ep) list |
    Ep_let of Location.loc * letbind * ep |
    Ep_let2 of Location.loc * SyntaxVCT.xp * SyntaxVCT.tau * ep * ep |
    Ep_if of Location.loc * ep * ep * ep | Ep_block of Location.loc * ep list |
    Ep_case of Location.loc * ep * pexpp list |
    Ep_assign of Location.loc * lexpp * ep * ep | Ep_exit of Location.loc * ep |
    Ep_return of Location.loc * ep | Ep_throw of Location.loc * ep |
    Ep_try of Location.loc * ep * pexpp list |
    Ep_constraint of Location.loc * SyntaxVCT.cp |
    Ep_loop of Location.loc * loop * ep * ep |
    Ep_for of Location.loc * string * ep * ep * ep * SyntaxVCT.order * ep |
    Ep_assert of Location.loc * ep * ep | Ep_vec of Location.loc * ep list |
    Ep_list of Location.loc * ep list | Ep_cons of Location.loc * ep * ep
  and pexpp = PEXPp_exp of patp * ep | PEXPp_when of patp * ep * ep
  and letbind = LBp_val of Location.loc * patp * ep
  type tannot_opt_p = Typ_annot_opt_pnone of Location.loc |
    Typ_annot_opt_psome of
      Location.loc * (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
        SyntaxVCT.tau
    | Typ_annot_opt_psome_fn of Location.loc * SyntaxVCT.ap
  type funclp = FCLp_funcl of Location.loc * string * pexpp
  type scattered_defp = SDp_function of Location.loc * tannot_opt_p * string |
    SDp_variant of
      Location.loc * string *
        (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
    | SDp_unioncl of Location.loc * string * string * SyntaxVCT.tau |
    SDp_funclp of Location.loc * funclp | SDp_end of Location.loc * string
  type def = DEFp_fundef of Location.loc * SyntaxVCT.ap * funclp list |
    DEFp_typedef of
      Location.loc * string *
        (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list * SyntaxVCT.tau
    | DEFp_spec of Location.loc * string * SyntaxVCT.ap |
    DEFp_val of Location.loc * letbind |
    DEFp_reg of Location.loc * SyntaxVCT.tau * SyntaxVCT.xp |
    DEFp_overload of Location.loc * string * string list |
    DEFp_scattered of Location.loc * scattered_defp |
    DEFp_default of Location.loc * SyntaxVCT.order
  type progp = Pp_prog of def list
  val fvs_vp : SyntaxVCT.vp -> SyntaxVCT.xp list
  val fvs_vp_list_V_vec : SyntaxVCT.vp list -> SyntaxVCT.xp list
  val fvs_vp_list_V_list : SyntaxVCT.vp list -> SyntaxVCT.xp list
  val fvs_vp_list_V_tuple : SyntaxVCT.vp list -> SyntaxVCT.xp list
  val fvs_field_vp_V_record : string * SyntaxVCT.vp -> SyntaxVCT.xp list
  val fvs_field_vp_list_V_record :
    (string * SyntaxVCT.vp) list -> SyntaxVCT.xp list
  val fvs_cep : SyntaxVCT.cep -> SyntaxVCT.xp list
  val fvs_cep_list : SyntaxVCT.cep list -> SyntaxVCT.xp list
  val fvs_cp : SyntaxVCT.cp -> SyntaxVCT.xp list
  val fvs_cp_list : SyntaxVCT.cp list -> SyntaxVCT.xp list
  val loc_e : ep -> Location.loc
  val subst_vp : SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.vp -> SyntaxVCT.vp
  val subst_vp_list_V_vec :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.vp list -> SyntaxVCT.vp list
  val subst_vp_list_V_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.vp list -> SyntaxVCT.vp list
  val subst_vp_list_V_tuple :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.vp list -> SyntaxVCT.vp list
  val subst_field_vp_V_record :
    SyntaxVCT.vp ->
      SyntaxVCT.xp -> string * SyntaxVCT.vp -> string * SyntaxVCT.vp
  val subst_field_vp_list_V_record :
    SyntaxVCT.vp ->
      SyntaxVCT.xp ->
        (string * SyntaxVCT.vp) list -> (string * SyntaxVCT.vp) list
  val subst_cep : SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.cep -> SyntaxVCT.cep
  val subst_cep_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.cep list -> SyntaxVCT.cep list
  val subst_cp : SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.cp -> SyntaxVCT.cp
  val subst_cp_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.cp list -> SyntaxVCT.cp list
  val subst_bp : SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.bp -> SyntaxVCT.bp
  val subst_tp : SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.tau -> SyntaxVCT.tau
  val subst_ctor_tau :
    SyntaxVCT.vp ->
      SyntaxVCT.xp -> string * SyntaxVCT.tau -> string * SyntaxVCT.tau
  val subst_ctor_tau_list :
    SyntaxVCT.vp ->
      SyntaxVCT.xp ->
        (string * SyntaxVCT.tau) list -> (string * SyntaxVCT.tau) list
  val subst_bp_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> SyntaxVCT.bp list -> SyntaxVCT.bp list
  val subst_field_bp :
    SyntaxVCT.vp ->
      SyntaxVCT.xp -> string * SyntaxVCT.bp -> string * SyntaxVCT.bp
  val subst_field_bp_list :
    SyntaxVCT.vp ->
      SyntaxVCT.xp ->
        (string * SyntaxVCT.bp) list -> (string * SyntaxVCT.bp) list
  val subst_patp : SyntaxVCT.vp -> SyntaxVCT.xp -> patp -> patp
  val subst_patp_list_Pp_app :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_patp_list_Pp_tup :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_patp_list_Pp_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_patp_list_Pp_vector :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_field_patp_Pp_record :
    SyntaxVCT.vp -> SyntaxVCT.xp -> string * patp -> string * patp
  val subst_field_patp_list_Pp_record :
    SyntaxVCT.vp -> SyntaxVCT.xp -> (string * patp) list -> (string * patp) list
  val subst_patp_list_Pp_string_append :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_patp_list_Pp_vector_concat :
    SyntaxVCT.vp -> SyntaxVCT.xp -> patp list -> patp list
  val subst_lexpp : SyntaxVCT.vp -> SyntaxVCT.xp -> lexpp -> lexpp
  val subst_lexpp_list :
    SyntaxVCT.vp -> SyntaxVCT.xp -> lexpp list -> lexpp list
  val subst_ep : SyntaxVCT.vp -> SyntaxVCT.xp -> ep -> ep
  val subst_pexpp : SyntaxVCT.vp -> SyntaxVCT.xp -> pexpp -> pexpp
  val subst_pexpp_list_Ep_try :
    SyntaxVCT.vp -> SyntaxVCT.xp -> pexpp list -> pexpp list
  val subst_pexpp_list_Ep_case :
    SyntaxVCT.vp -> SyntaxVCT.xp -> pexpp list -> pexpp list
  val subst_letbind : SyntaxVCT.vp -> SyntaxVCT.xp -> letbind -> letbind
  val subst_ep_list_Ep_vec : SyntaxVCT.vp -> SyntaxVCT.xp -> ep list -> ep list
  val subst_ep_list_Ep_list : SyntaxVCT.vp -> SyntaxVCT.xp -> ep list -> ep list
  val subst_ep_list_Ep_block :
    SyntaxVCT.vp -> SyntaxVCT.xp -> ep list -> ep list
  val subst_ep_list_Ep_tuple :
    SyntaxVCT.vp -> SyntaxVCT.xp -> ep list -> ep list
  val subst_ep_list_Ep_concat :
    SyntaxVCT.vp -> SyntaxVCT.xp -> ep list -> ep list
  val subst_field_ep_Ep_record :
    SyntaxVCT.vp -> SyntaxVCT.xp -> string * ep -> string * ep
  val subst_field_ep_list_Ep_record :
    SyntaxVCT.vp -> SyntaxVCT.xp -> (string * ep) list -> (string * ep) list
  val subst_field_ep_Ep_record_update :
    SyntaxVCT.vp -> SyntaxVCT.xp -> string * ep -> string * ep
  val subst_field_ep_list_Ep_record_update :
    SyntaxVCT.vp -> SyntaxVCT.xp -> (string * ep) list -> (string * ep) list
  val tsubst_bp : SyntaxVCT.bp -> string -> SyntaxVCT.bp -> SyntaxVCT.bp
  val tsubst_tp : SyntaxVCT.bp -> string -> SyntaxVCT.tau -> SyntaxVCT.tau
  val tsubst_ctor_tau :
    SyntaxVCT.bp -> string -> string * SyntaxVCT.tau -> string * SyntaxVCT.tau
  val tsubst_ctor_tau_list :
    SyntaxVCT.bp ->
      string -> (string * SyntaxVCT.tau) list -> (string * SyntaxVCT.tau) list
  val tsubst_bp_list :
    SyntaxVCT.bp -> string -> SyntaxVCT.bp list -> SyntaxVCT.bp list
  val tsubst_field_bp :
    SyntaxVCT.bp -> string -> string * SyntaxVCT.bp -> string * SyntaxVCT.bp
  val tsubst_field_bp_list :
    SyntaxVCT.bp ->
      string -> (string * SyntaxVCT.bp) list -> (string * SyntaxVCT.bp) list
  val ce_subst_cep :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.cep -> SyntaxVCT.cep
  val ce_subst_cep_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.cep list -> SyntaxVCT.cep list
  val ce_subst_cp :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.cp -> SyntaxVCT.cp
  val ce_subst_cp_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.cp list -> SyntaxVCT.cp list
  val ce_subst_bp :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.bp -> SyntaxVCT.bp
  val ce_subst_tp :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.tau -> SyntaxVCT.tau
  val ce_subst_ctor_tau :
    SyntaxVCT.cep ->
      SyntaxVCT.xp -> string * SyntaxVCT.tau -> string * SyntaxVCT.tau
  val ce_subst_ctor_tau_list :
    SyntaxVCT.cep ->
      SyntaxVCT.xp ->
        (string * SyntaxVCT.tau) list -> (string * SyntaxVCT.tau) list
  val ce_subst_bp_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> SyntaxVCT.bp list -> SyntaxVCT.bp list
  val ce_subst_field_bp :
    SyntaxVCT.cep ->
      SyntaxVCT.xp -> string * SyntaxVCT.bp -> string * SyntaxVCT.bp
  val ce_subst_field_bp_list :
    SyntaxVCT.cep ->
      SyntaxVCT.xp ->
        (string * SyntaxVCT.bp) list -> (string * SyntaxVCT.bp) list
  val ce_subst_patp : SyntaxVCT.cep -> SyntaxVCT.xp -> patp -> patp
  val ce_subst_patp_list_Pp_app :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_patp_list_Pp_tup :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_patp_list_Pp_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_patp_list_Pp_vector :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_field_patp_Pp_record :
    SyntaxVCT.cep -> SyntaxVCT.xp -> string * patp -> string * patp
  val ce_subst_field_patp_list_Pp_record :
    SyntaxVCT.cep ->
      SyntaxVCT.xp -> (string * patp) list -> (string * patp) list
  val ce_subst_patp_list_Pp_string_append :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_patp_list_Pp_vector_concat :
    SyntaxVCT.cep -> SyntaxVCT.xp -> patp list -> patp list
  val ce_subst_lexpp : SyntaxVCT.cep -> SyntaxVCT.xp -> lexpp -> lexpp
  val ce_subst_lexpp_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> lexpp list -> lexpp list
  val ce_subst_ep : SyntaxVCT.cep -> SyntaxVCT.xp -> ep -> ep
  val ce_subst_pexpp : SyntaxVCT.cep -> SyntaxVCT.xp -> pexpp -> pexpp
  val ce_subst_pexpp_list_Ep_try :
    SyntaxVCT.cep -> SyntaxVCT.xp -> pexpp list -> pexpp list
  val ce_subst_pexpp_list_Ep_case :
    SyntaxVCT.cep -> SyntaxVCT.xp -> pexpp list -> pexpp list
  val ce_subst_letbind : SyntaxVCT.cep -> SyntaxVCT.xp -> letbind -> letbind
  val ce_subst_ep_list_Ep_vec :
    SyntaxVCT.cep -> SyntaxVCT.xp -> ep list -> ep list
  val ce_subst_ep_list_Ep_list :
    SyntaxVCT.cep -> SyntaxVCT.xp -> ep list -> ep list
  val ce_subst_ep_list_Ep_block :
    SyntaxVCT.cep -> SyntaxVCT.xp -> ep list -> ep list
  val ce_subst_ep_list_Ep_tuple :
    SyntaxVCT.cep -> SyntaxVCT.xp -> ep list -> ep list
  val ce_subst_ep_list_Ep_concat :
    SyntaxVCT.cep -> SyntaxVCT.xp -> ep list -> ep list
  val ce_subst_field_ep_Ep_record :
    SyntaxVCT.cep -> SyntaxVCT.xp -> string * ep -> string * ep
  val ce_subst_field_ep_list_Ep_record :
    SyntaxVCT.cep -> SyntaxVCT.xp -> (string * ep) list -> (string * ep) list
  val ce_subst_field_ep_Ep_record_update :
    SyntaxVCT.cep -> SyntaxVCT.xp -> string * ep -> string * ep
  val ce_subst_field_ep_list_Ep_record_update :
    SyntaxVCT.cep -> SyntaxVCT.xp -> (string * ep) list -> (string * ep) list
  val ce_subst_funclp : SyntaxVCT.cep -> SyntaxVCT.xp -> funclp -> funclp
end = struct

type patp = Pp_id of Location.loc * string | Pp_wild of Location.loc |
  Pp_lit of Location.loc * SyntaxVCT.lit |
  Pp_typ of Location.loc * SyntaxVCT.tau * patp |
  Pp_app of Location.loc * string * patp list |
  Pp_tup of Location.loc * patp list |
  Pp_vector_concat of Location.loc * patp list |
  Pp_as_var of Location.loc * patp * SyntaxVCT.xp |
  Pp_as_typ of Location.loc * patp * SyntaxVCT.tau |
  Pp_cons of Location.loc * patp * patp |
  Pp_string_append of Location.loc * patp list |
  Pp_vector of Location.loc * patp list | Pp_list of Location.loc * patp list |
  Pp_record of Location.loc * (string * patp) list;;

type lexpp = LEXPp_mvar of Location.loc * string |
  LEXPp_cast of Location.loc * SyntaxVCT.tau * string |
  LEXPp_tup of Location.loc * lexpp list |
  LEXPp_field of Location.loc * lexpp * string;;

type loop = While | Until;;

type ep = Ep_val of Location.loc * SyntaxVCT.vp |
  Ep_mvar of Location.loc * string | Ep_concat of Location.loc * ep list |
  Ep_tuple of Location.loc * ep list |
  Ep_app of Location.loc * SyntaxVCT.xp * ep |
  Ep_bop of Location.loc * SyntaxVCT.bop * ep * ep |
  Ep_uop of Location.loc * SyntaxVCT.uop * ep |
  Ep_proj of Location.loc * string * ep |
  Ep_constr of Location.loc * string * ep |
  Ep_field_access of Location.loc * ep * string |
  Ep_sizeof of Location.loc * SyntaxVCT.cep |
  Ep_cast of Location.loc * SyntaxVCT.tau * ep |
  Ep_record of Location.loc * (string * ep) list |
  Ep_record_update of Location.loc * ep * (string * ep) list |
  Ep_let of Location.loc * letbind * ep |
  Ep_let2 of Location.loc * SyntaxVCT.xp * SyntaxVCT.tau * ep * ep |
  Ep_if of Location.loc * ep * ep * ep | Ep_block of Location.loc * ep list |
  Ep_case of Location.loc * ep * pexpp list |
  Ep_assign of Location.loc * lexpp * ep * ep | Ep_exit of Location.loc * ep |
  Ep_return of Location.loc * ep | Ep_throw of Location.loc * ep |
  Ep_try of Location.loc * ep * pexpp list |
  Ep_constraint of Location.loc * SyntaxVCT.cp |
  Ep_loop of Location.loc * loop * ep * ep |
  Ep_for of Location.loc * string * ep * ep * ep * SyntaxVCT.order * ep |
  Ep_assert of Location.loc * ep * ep | Ep_vec of Location.loc * ep list |
  Ep_list of Location.loc * ep list | Ep_cons of Location.loc * ep * ep
and pexpp = PEXPp_exp of patp * ep | PEXPp_when of patp * ep * ep
and letbind = LBp_val of Location.loc * patp * ep;;

type tannot_opt_p = Typ_annot_opt_pnone of Location.loc |
  Typ_annot_opt_psome of
    Location.loc * (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list *
      SyntaxVCT.tau
  | Typ_annot_opt_psome_fn of Location.loc * SyntaxVCT.ap;;

type funclp = FCLp_funcl of Location.loc * string * pexpp;;

type scattered_defp = SDp_function of Location.loc * tannot_opt_p * string |
  SDp_variant of
    Location.loc * string * (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  | SDp_unioncl of Location.loc * string * string * SyntaxVCT.tau |
  SDp_funclp of Location.loc * funclp | SDp_end of Location.loc * string;;

type def = DEFp_fundef of Location.loc * SyntaxVCT.ap * funclp list |
  DEFp_typedef of
    Location.loc * string *
      (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list * SyntaxVCT.tau
  | DEFp_spec of Location.loc * string * SyntaxVCT.ap |
  DEFp_val of Location.loc * letbind |
  DEFp_reg of Location.loc * SyntaxVCT.tau * SyntaxVCT.xp |
  DEFp_overload of Location.loc * string * string list |
  DEFp_scattered of Location.loc * scattered_defp |
  DEFp_default of Location.loc * SyntaxVCT.order;;

type progp = Pp_prog of def list;;

let rec fvs_vp
  = function SyntaxVCT.V_lit lit -> []
    | SyntaxVCT.V_var xp -> [xp]
    | SyntaxVCT.V_vec vp_list -> fvs_vp_list_V_vec vp_list
    | SyntaxVCT.V_list vp_list -> fvs_vp_list_V_list vp_list
    | SyntaxVCT.V_cons (vp1, vp2) -> fvs_vp vp1 @ fvs_vp vp2
    | SyntaxVCT.V_constr (ctor, vp) -> fvs_vp vp
    | SyntaxVCT.V_record field_vp_list ->
        fvs_field_vp_list_V_record field_vp_list
    | SyntaxVCT.V_tuple vp_list -> fvs_vp_list_V_tuple vp_list
    | SyntaxVCT.V_proj (p, vp) -> fvs_vp vp
and fvs_vp_list_V_vec
  = function [] -> []
    | vp_XXX :: vp_list_XXX -> fvs_vp vp_XXX @ fvs_vp_list_V_vec vp_list_XXX
and fvs_vp_list_V_list
  = function [] -> []
    | vp_XXX :: vp_list_XXX -> fvs_vp vp_XXX @ fvs_vp_list_V_list vp_list_XXX
and fvs_vp_list_V_tuple
  = function [] -> []
    | vp_XXX :: vp_list_XXX -> fvs_vp vp_XXX @ fvs_vp_list_V_tuple vp_list_XXX
and fvs_field_vp_V_record (field_XXX, vp_XXX) = fvs_vp vp_XXX
and fvs_field_vp_list_V_record
  = function [] -> []
    | field_vp_XXX :: field_vp_list_XXX ->
        fvs_field_vp_V_record field_vp_XXX @
          fvs_field_vp_list_V_record field_vp_list_XXX;;

let rec fvs_cep
  = function SyntaxVCT.CE_val vp -> fvs_vp vp
    | SyntaxVCT.CE_bop (bop, cep1, cep2) -> fvs_cep cep1 @ fvs_cep cep2
    | SyntaxVCT.CE_many_plus cep_list -> fvs_cep_list cep_list
    | SyntaxVCT.CE_uop (uop, cep) -> fvs_cep cep
    | SyntaxVCT.CE_proj (p, cep) -> fvs_cep cep
    | SyntaxVCT.CE_field_access (xp, field) -> []
and fvs_cep_list
  = function [] -> []
    | cep_XXX :: cep_list_XXX -> fvs_cep cep_XXX @ fvs_cep_list cep_list_XXX;;

let rec fvs_cp = function SyntaxVCT.C_true -> []
                 | SyntaxVCT.C_false -> []
                 | SyntaxVCT.C_conj (cp1, cp2) -> fvs_cp cp1 @ fvs_cp cp2
                 | SyntaxVCT.C_conj_many cp_list -> fvs_cp_list cp_list
                 | SyntaxVCT.C_disj (cp1, cp2) -> fvs_cp cp1 @ fvs_cp cp2
                 | SyntaxVCT.C_not cp -> fvs_cp cp
                 | SyntaxVCT.C_eq (cep1, cep2) -> fvs_cep cep1 @ fvs_cep cep2
                 | SyntaxVCT.C_leq (cep1, cep2) -> fvs_cep cep1 @ fvs_cep cep2
                 | SyntaxVCT.C_imp (cp1, cp2) -> fvs_cp cp1 @ fvs_cp cp2
and fvs_cp_list
  = function [] -> []
    | cp_XXX :: cp_list_XXX -> fvs_cp cp_XXX @ fvs_cp_list cp_list_XXX;;

let rec loc_e = function Ep_val (x11, x12) -> x11
                | Ep_mvar (x21, x22) -> x21
                | Ep_concat (x31, x32) -> x31
                | Ep_tuple (x41, x42) -> x41
                | Ep_app (x51, x52, x53) -> x51
                | Ep_bop (x61, x62, x63, x64) -> x61
                | Ep_uop (x71, x72, x73) -> x71
                | Ep_proj (x81, x82, x83) -> x81
                | Ep_constr (x91, x92, x93) -> x91
                | Ep_field_access (x101, x102, x103) -> x101
                | Ep_sizeof (x111, x112) -> x111
                | Ep_cast (x121, x122, x123) -> x121
                | Ep_record (x131, x132) -> x131
                | Ep_record_update (x141, x142, x143) -> x141
                | Ep_let (x151, x152, x153) -> x151
                | Ep_let2 (x161, x162, x163, x164, x165) -> x161
                | Ep_if (x171, x172, x173, x174) -> x171
                | Ep_block (x181, x182) -> x181
                | Ep_case (x191, x192, x193) -> x191
                | Ep_assign (x201, x202, x203, x204) -> x201
                | Ep_exit (x211, x212) -> x211
                | Ep_return (x221, x222) -> x221
                | Ep_throw (x231, x232) -> x231
                | Ep_try (x241, x242, x243) -> x241
                | Ep_constraint (x251, x252) -> x251
                | Ep_loop (x261, x262, x263, x264) -> x261
                | Ep_for (x271, x272, x273, x274, x275, x276, x277) -> x271
                | Ep_assert (x281, x282, x283) -> x281
                | Ep_vec (x291, x292) -> x291
                | Ep_list (x301, x302) -> x301
                | Ep_cons (x311, x312, x313) -> x311;;

let rec subst_vp
  vp_5 zp5 x2 = match vp_5, zp5, x2 with
    vp_5, zp5, SyntaxVCT.V_lit lit -> SyntaxVCT.V_lit lit
    | vp_5, zp5, SyntaxVCT.V_var xp ->
        (if SyntaxVCT.equal_xpa xp zp5 then vp_5 else SyntaxVCT.V_var xp)
    | vp_5, zp5, SyntaxVCT.V_vec vp_list ->
        SyntaxVCT.V_vec (subst_vp_list_V_vec vp_5 zp5 vp_list)
    | vp_5, zp5, SyntaxVCT.V_list vp_list ->
        SyntaxVCT.V_list (subst_vp_list_V_list vp_5 zp5 vp_list)
    | vp_5, zp5, SyntaxVCT.V_cons (vp1, vp2) ->
        SyntaxVCT.V_cons (subst_vp vp_5 zp5 vp1, subst_vp vp_5 zp5 vp2)
    | vp_5, zp5, SyntaxVCT.V_constr (ctor, vp) ->
        SyntaxVCT.V_constr (ctor, subst_vp vp_5 zp5 vp)
    | vp_5, zp5, SyntaxVCT.V_record field_vp_list ->
        SyntaxVCT.V_record (subst_field_vp_list_V_record vp_5 zp5 field_vp_list)
    | vp_5, zp5, SyntaxVCT.V_tuple vp_list ->
        SyntaxVCT.V_tuple (subst_vp_list_V_tuple vp_5 zp5 vp_list)
    | vp_5, zp5, SyntaxVCT.V_proj (p, vp) ->
        SyntaxVCT.V_proj (p, subst_vp vp_5 zp5 vp)
and subst_vp_list_V_vec
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_vec vp_5 zp5 vp_list_XXX
and subst_vp_list_V_list
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_list vp_5 zp5 vp_list_XXX
and subst_vp_list_V_tuple
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, vp_XXX :: vp_list_XXX ->
        subst_vp vp_5 zp5 vp_XXX :: subst_vp_list_V_tuple vp_5 zp5 vp_list_XXX
and subst_field_vp_V_record
  vp_5 zp5 (field1, vp1) = (field1, subst_vp vp_5 zp5 vp1)
and subst_field_vp_list_V_record
  vp_5 zp5 x2 = match vp_5, zp5, x2 with vp_5, zp5, [] -> []
    | vp_5, zp5, field_vp_XXX :: field_vp_list_XXX ->
        subst_field_vp_V_record vp_5 zp5 field_vp_XXX ::
          subst_field_vp_list_V_record vp_5 zp5 field_vp_list_XXX;;

let rec subst_cep
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, SyntaxVCT.CE_val vp -> SyntaxVCT.CE_val (subst_vp vp5 zp5 vp)
    | vp5, zp5, SyntaxVCT.CE_bop (bop, cep1, cep2) ->
        SyntaxVCT.CE_bop (bop, subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, SyntaxVCT.CE_many_plus cep_list ->
        SyntaxVCT.CE_many_plus (subst_cep_list vp5 zp5 cep_list)
    | vp5, zp5, SyntaxVCT.CE_uop (uop, cep) ->
        SyntaxVCT.CE_uop (uop, subst_cep vp5 zp5 cep)
    | vp5, zp5, SyntaxVCT.CE_proj (p, cep) ->
        SyntaxVCT.CE_proj (p, subst_cep vp5 zp5 cep)
    | vp5, zp5, SyntaxVCT.CE_field_access (xp, field) ->
        SyntaxVCT.CE_field_access (xp, field)
and subst_cep_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, cep_XXX :: cep_list_XXX ->
        subst_cep vp5 zp5 cep_XXX :: subst_cep_list vp5 zp5 cep_list_XXX;;

let rec subst_cp
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, SyntaxVCT.C_true -> SyntaxVCT.C_true
    | vp5, zp5, SyntaxVCT.C_false -> SyntaxVCT.C_false
    | vp5, zp5, SyntaxVCT.C_conj (cp1, cp2) ->
        SyntaxVCT.C_conj (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
    | vp5, zp5, SyntaxVCT.C_conj_many cp_list ->
        SyntaxVCT.C_conj_many (subst_cp_list vp5 zp5 cp_list)
    | vp5, zp5, SyntaxVCT.C_disj (cp1, cp2) ->
        SyntaxVCT.C_disj (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
    | vp5, zp5, SyntaxVCT.C_not cp -> SyntaxVCT.C_not (subst_cp vp5 zp5 cp)
    | vp5, zp5, SyntaxVCT.C_eq (cep1, cep2) ->
        SyntaxVCT.C_eq (subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, SyntaxVCT.C_leq (cep1, cep2) ->
        SyntaxVCT.C_leq (subst_cep vp5 zp5 cep1, subst_cep vp5 zp5 cep2)
    | vp5, zp5, SyntaxVCT.C_imp (cp1, cp2) ->
        SyntaxVCT.C_imp (subst_cp vp5 zp5 cp1, subst_cp vp5 zp5 cp2)
and subst_cp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, cp_XXX :: cp_list_XXX ->
        subst_cp vp5 zp5 cp_XXX :: subst_cp_list vp5 zp5 cp_list_XXX;;

let rec subst_bp
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, SyntaxVCT.B_var tvar -> SyntaxVCT.B_var tvar
    | vp5, zp5, SyntaxVCT.B_tid id -> SyntaxVCT.B_tid id
    | vp5, zp5, SyntaxVCT.B_int -> SyntaxVCT.B_int
    | vp5, zp5, SyntaxVCT.B_bool -> SyntaxVCT.B_bool
    | vp5, zp5, SyntaxVCT.B_bit -> SyntaxVCT.B_bit
    | vp5, zp5, SyntaxVCT.B_unit -> SyntaxVCT.B_unit
    | vp5, zp5, SyntaxVCT.B_real -> SyntaxVCT.B_real
    | vp5, zp5, SyntaxVCT.B_vec (order, bp) ->
        SyntaxVCT.B_vec (order, subst_bp vp5 zp5 bp)
    | vp5, zp5, SyntaxVCT.B_list bp -> SyntaxVCT.B_list (subst_bp vp5 zp5 bp)
    | vp5, zp5, SyntaxVCT.B_tuple bp_list ->
        SyntaxVCT.B_tuple (subst_bp_list vp5 zp5 bp_list)
    | vp5, zp5, SyntaxVCT.B_union (id, ctor_tau_list) ->
        SyntaxVCT.B_union (id, subst_ctor_tau_list vp5 zp5 ctor_tau_list)
    | vp5, zp5, SyntaxVCT.B_record field_bp_list ->
        SyntaxVCT.B_record (subst_field_bp_list vp5 zp5 field_bp_list)
    | vp5, zp5, SyntaxVCT.B_undef -> SyntaxVCT.B_undef
    | vp5, zp5, SyntaxVCT.B_reg -> SyntaxVCT.B_reg
    | vp5, zp5, SyntaxVCT.B_string -> SyntaxVCT.B_string
    | vp5, zp5, SyntaxVCT.B_exception -> SyntaxVCT.B_exception
    | vp5, zp5, SyntaxVCT.B_finite_set num_list ->
        SyntaxVCT.B_finite_set num_list
and subst_tp
  vp5 zp5 (SyntaxVCT.T_refined_type (zp, bp, cp)) =
    SyntaxVCT.T_refined_type (zp, subst_bp vp5 zp5 bp, subst_cp vp5 zp5 cp)
and subst_ctor_tau vp5 zp5 (ctor1, tp1) = (ctor1, subst_tp vp5 zp5 tp1)
and subst_ctor_tau_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ctor_tau_XXX :: ctor_tau_list_XXX ->
        subst_ctor_tau vp5 zp5 ctor_tau_XXX ::
          subst_ctor_tau_list vp5 zp5 ctor_tau_list_XXX
and subst_bp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, bp_XXX :: bp_list_XXX ->
        subst_bp vp5 zp5 bp_XXX :: subst_bp_list vp5 zp5 bp_list_XXX
and subst_field_bp vp5 zp5 (field1, bp1) = (field1, subst_bp vp5 zp5 bp1)
and subst_field_bp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, field_bp_XXX :: field_bp_list_XXX ->
        subst_field_bp vp5 zp5 field_bp_XXX ::
          subst_field_bp_list vp5 zp5 field_bp_list_XXX;;

let rec subst_patp
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, Pp_id (loc, id) -> Pp_id (loc, id)
    | vp5, zp5, Pp_wild loc -> Pp_wild loc
    | vp5, zp5, Pp_lit (loc, lit) -> Pp_lit (loc, lit)
    | vp5, zp5, Pp_typ (loc, tau, patp) ->
        Pp_typ (loc, subst_tp vp5 zp5 tau, subst_patp vp5 zp5 patp)
    | vp5, zp5, Pp_app (loc, id, patp_list) ->
        Pp_app (loc, id, subst_patp_list_Pp_app vp5 zp5 patp_list)
    | vp5, zp5, Pp_tup (loc, patp_list) ->
        Pp_tup (loc, subst_patp_list_Pp_tup vp5 zp5 patp_list)
    | vp5, zp5, Pp_vector_concat (loc, patp_list) ->
        Pp_vector_concat
          (loc, subst_patp_list_Pp_vector_concat vp5 zp5 patp_list)
    | vp5, zp5, Pp_as_var (loc, patp, xp) ->
        Pp_as_var (loc, subst_patp vp5 zp5 patp, xp)
    | vp5, zp5, Pp_as_typ (loc, patp, tau) ->
        Pp_as_typ (loc, subst_patp vp5 zp5 patp, subst_tp vp5 zp5 tau)
    | vp5, zp5, Pp_cons (loc, patp1, patp2) ->
        Pp_cons (loc, subst_patp vp5 zp5 patp1, subst_patp vp5 zp5 patp2)
    | vp5, zp5, Pp_string_append (loc, patp_list) ->
        Pp_string_append
          (loc, subst_patp_list_Pp_string_append vp5 zp5 patp_list)
    | vp5, zp5, Pp_vector (loc, patp_list) ->
        Pp_vector (loc, subst_patp_list_Pp_vector vp5 zp5 patp_list)
    | vp5, zp5, Pp_list (loc, patp_list) ->
        Pp_list (loc, subst_patp_list_Pp_list vp5 zp5 patp_list)
    | vp5, zp5, Pp_record (loc, field_patp_list) ->
        Pp_record (loc, subst_field_patp_list_Pp_record vp5 zp5 field_patp_list)
and subst_patp_list_Pp_app
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_app vp5 zp5 patp_list_XXX
and subst_patp_list_Pp_tup
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_tup vp5 zp5 patp_list_XXX
and subst_patp_list_Pp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_list vp5 zp5 patp_list_XXX
and subst_patp_list_Pp_vector
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_vector vp5 zp5 patp_list_XXX
and subst_field_patp_Pp_record
  vp5 zp5 (field1, patp1) = (field1, subst_patp vp5 zp5 patp1)
and subst_field_patp_list_Pp_record
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, field_patp_XXX :: field_patp_list_XXX ->
        subst_field_patp_Pp_record vp5 zp5 field_patp_XXX ::
          subst_field_patp_list_Pp_record vp5 zp5 field_patp_list_XXX
and subst_patp_list_Pp_string_append
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_string_append vp5 zp5 patp_list_XXX
and subst_patp_list_Pp_vector_concat
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, patp_XXX :: patp_list_XXX ->
        subst_patp vp5 zp5 patp_XXX ::
          subst_patp_list_Pp_vector_concat vp5 zp5 patp_list_XXX;;

let rec subst_lexpp
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, LEXPp_mvar (loc, up) -> LEXPp_mvar (loc, up)
    | vp5, zp5, LEXPp_cast (loc, tau, up) ->
        LEXPp_cast (loc, subst_tp vp5 zp5 tau, up)
    | vp5, zp5, LEXPp_tup (loc, lexpp_list) ->
        LEXPp_tup (loc, subst_lexpp_list vp5 zp5 lexpp_list)
    | vp5, zp5, LEXPp_field (loc, lexpp, id) ->
        LEXPp_field (loc, subst_lexpp vp5 zp5 lexpp, id)
and subst_lexpp_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, lexpp_XXX :: lexpp_list_XXX ->
        subst_lexpp vp5 zp5 lexpp_XXX ::
          subst_lexpp_list vp5 zp5 lexpp_list_XXX;;

let rec subst_ep
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, Ep_val (loc, vp) -> Ep_val (loc, subst_vp vp5 zp5 vp)
    | vp5, zp5, Ep_mvar (loc, up) -> Ep_mvar (loc, up)
    | vp5, zp5, Ep_concat (loc, ep_list) ->
        Ep_concat (loc, subst_ep_list_Ep_concat vp5 zp5 ep_list)
    | vp5, zp5, Ep_tuple (loc, ep_list) ->
        Ep_tuple (loc, subst_ep_list_Ep_tuple vp5 zp5 ep_list)
    | vp5, zp5, Ep_app (loc, fp, ep) -> Ep_app (loc, fp, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_bop (loc, bop, ep1, ep2) ->
        Ep_bop (loc, bop, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2)
    | vp5, zp5, Ep_uop (loc, uop, ep) -> Ep_uop (loc, uop, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_proj (loc, p, ep) -> Ep_proj (loc, p, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_constr (loc, ctor, ep) ->
        Ep_constr (loc, ctor, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_field_access (loc, ep, field) ->
        Ep_field_access (loc, subst_ep vp5 zp5 ep, field)
    | vp5, zp5, Ep_sizeof (loc, cep) -> Ep_sizeof (loc, subst_cep vp5 zp5 cep)
    | vp5, zp5, Ep_cast (loc, tau, ep) ->
        Ep_cast (loc, subst_tp vp5 zp5 tau, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_record (loc, field_ep_list) ->
        Ep_record (loc, subst_field_ep_list_Ep_record vp5 zp5 field_ep_list)
    | vp5, zp5, Ep_record_update (loc, ep, field_ep_list) ->
        Ep_record_update
          (loc, subst_ep vp5 zp5 ep,
            subst_field_ep_list_Ep_record_update vp5 zp5 field_ep_list)
    | vp5, zp5, Ep_let (loc, letbind, ep2) ->
        Ep_let (loc, subst_letbind vp5 zp5 letbind, subst_ep vp5 zp5 ep2)
    | vp5, zp5, Ep_let2 (loc, xp, tau, ep1, ep2) ->
        Ep_let2
          (loc, xp, subst_tp vp5 zp5 tau, subst_ep vp5 zp5 ep1,
            (if Lista.member SyntaxVCT.equal_xp [xp] zp5 then ep2
              else subst_ep vp5 zp5 ep2))
    | vp5, zp5, Ep_if (loc, ep1, ep2, ep3) ->
        Ep_if (loc, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2,
                subst_ep vp5 zp5 ep3)
    | vp5, zp5, Ep_block (loc, ep_list) ->
        Ep_block (loc, subst_ep_list_Ep_block vp5 zp5 ep_list)
    | vp5, zp5, Ep_case (loc, ep, pexpp_list) ->
        Ep_case
          (loc, subst_ep vp5 zp5 ep,
            subst_pexpp_list_Ep_case vp5 zp5 pexpp_list)
    | vp5, zp5, Ep_assign (loc, lexpp, ep1, ep2) ->
        Ep_assign
          (loc, subst_lexpp vp5 zp5 lexpp, subst_ep vp5 zp5 ep1,
            subst_ep vp5 zp5 ep2)
    | vp5, zp5, Ep_exit (loc, ep) -> Ep_exit (loc, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_return (loc, ep) -> Ep_return (loc, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_throw (loc, ep) -> Ep_throw (loc, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_try (loc, ep, pexpp_list) ->
        Ep_try
          (loc, subst_ep vp5 zp5 ep, subst_pexpp_list_Ep_try vp5 zp5 pexpp_list)
    | vp5, zp5, Ep_constraint (loc, cp) ->
        Ep_constraint (loc, subst_cp vp5 zp5 cp)
    | vp5, zp5, Ep_loop (loc, loop, ep1, ep2) ->
        Ep_loop (loc, loop, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2)
    | vp5, zp5, Ep_for (loc, id, ep1, ep2, ep3, order, ep4) ->
        Ep_for
          (loc, id, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2,
            subst_ep vp5 zp5 ep3, order, subst_ep vp5 zp5 ep4)
    | vp5, zp5, Ep_assert (loc, ep1, ep2) ->
        Ep_assert (loc, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2)
    | vp5, zp5, Ep_vec (loc, ep_list) ->
        Ep_vec (loc, subst_ep_list_Ep_vec vp5 zp5 ep_list)
    | vp5, zp5, Ep_list (loc, ep_list) ->
        Ep_list (loc, subst_ep_list_Ep_list vp5 zp5 ep_list)
    | vp5, zp5, Ep_cons (loc, ep1, ep2) ->
        Ep_cons (loc, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2)
and subst_pexpp
  vp5 zp5 x2 = match vp5, zp5, x2 with
    vp5, zp5, PEXPp_exp (patp, ep) ->
      PEXPp_exp (subst_patp vp5 zp5 patp, subst_ep vp5 zp5 ep)
    | vp5, zp5, PEXPp_when (patp, ep1, ep2) ->
        PEXPp_when
          (subst_patp vp5 zp5 patp, subst_ep vp5 zp5 ep1, subst_ep vp5 zp5 ep2)
and subst_pexpp_list_Ep_try
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, pexpp_XXX :: pexpp_list_XXX ->
        subst_pexpp vp5 zp5 pexpp_XXX ::
          subst_pexpp_list_Ep_try vp5 zp5 pexpp_list_XXX
and subst_pexpp_list_Ep_case
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, pexpp_XXX :: pexpp_list_XXX ->
        subst_pexpp vp5 zp5 pexpp_XXX ::
          subst_pexpp_list_Ep_case vp5 zp5 pexpp_list_XXX
and subst_letbind
  vp5 zp5 (LBp_val (loc, patp, ep)) =
    LBp_val (loc, subst_patp vp5 zp5 patp, subst_ep vp5 zp5 ep)
and subst_ep_list_Ep_vec
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ep_XXX :: ep_list_XXX ->
        subst_ep vp5 zp5 ep_XXX :: subst_ep_list_Ep_vec vp5 zp5 ep_list_XXX
and subst_ep_list_Ep_list
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ep_XXX :: ep_list_XXX ->
        subst_ep vp5 zp5 ep_XXX :: subst_ep_list_Ep_list vp5 zp5 ep_list_XXX
and subst_ep_list_Ep_block
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ep_XXX :: ep_list_XXX ->
        subst_ep vp5 zp5 ep_XXX :: subst_ep_list_Ep_block vp5 zp5 ep_list_XXX
and subst_ep_list_Ep_tuple
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ep_XXX :: ep_list_XXX ->
        subst_ep vp5 zp5 ep_XXX :: subst_ep_list_Ep_tuple vp5 zp5 ep_list_XXX
and subst_ep_list_Ep_concat
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, ep_XXX :: ep_list_XXX ->
        subst_ep vp5 zp5 ep_XXX :: subst_ep_list_Ep_concat vp5 zp5 ep_list_XXX
and subst_field_ep_Ep_record
  vp5 zp5 (field1, ep1) = (field1, subst_ep vp5 zp5 ep1)
and subst_field_ep_list_Ep_record
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, field_ep_XXX :: field_ep_list_XXX ->
        subst_field_ep_Ep_record vp5 zp5 field_ep_XXX ::
          subst_field_ep_list_Ep_record vp5 zp5 field_ep_list_XXX
and subst_field_ep_Ep_record_update
  vp5 zp5 (field1, ep1) = (field1, subst_ep vp5 zp5 ep1)
and subst_field_ep_list_Ep_record_update
  vp5 zp5 x2 = match vp5, zp5, x2 with vp5, zp5, [] -> []
    | vp5, zp5, field_ep_XXX :: field_ep_list_XXX ->
        subst_field_ep_Ep_record_update vp5 zp5 field_ep_XXX ::
          subst_field_ep_list_Ep_record_update vp5 zp5 field_ep_list_XXX;;

let rec tsubst_bp
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with
    bp_5, tvar5, SyntaxVCT.B_var tvar ->
      (if ((tvar : string) = tvar5) then bp_5 else SyntaxVCT.B_var tvar)
    | bp_5, tvar5, SyntaxVCT.B_tid id -> SyntaxVCT.B_tid id
    | bp_5, tvar5, SyntaxVCT.B_int -> SyntaxVCT.B_int
    | bp_5, tvar5, SyntaxVCT.B_bool -> SyntaxVCT.B_bool
    | bp_5, tvar5, SyntaxVCT.B_bit -> SyntaxVCT.B_bit
    | bp_5, tvar5, SyntaxVCT.B_unit -> SyntaxVCT.B_unit
    | bp_5, tvar5, SyntaxVCT.B_real -> SyntaxVCT.B_real
    | bp_5, tvar5, SyntaxVCT.B_vec (order, bp) ->
        SyntaxVCT.B_vec (order, tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, SyntaxVCT.B_list bp ->
        SyntaxVCT.B_list (tsubst_bp bp_5 tvar5 bp)
    | bp_5, tvar5, SyntaxVCT.B_tuple bp_list ->
        SyntaxVCT.B_tuple (tsubst_bp_list bp_5 tvar5 bp_list)
    | bp_5, tvar5, SyntaxVCT.B_union (id, ctor_tau_list) ->
        SyntaxVCT.B_union (id, tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list)
    | bp_5, tvar5, SyntaxVCT.B_record field_bp_list ->
        SyntaxVCT.B_record (tsubst_field_bp_list bp_5 tvar5 field_bp_list)
    | bp_5, tvar5, SyntaxVCT.B_undef -> SyntaxVCT.B_undef
    | bp_5, tvar5, SyntaxVCT.B_reg -> SyntaxVCT.B_reg
    | bp_5, tvar5, SyntaxVCT.B_string -> SyntaxVCT.B_string
    | bp_5, tvar5, SyntaxVCT.B_exception -> SyntaxVCT.B_exception
    | bp_5, tvar5, SyntaxVCT.B_finite_set num_list ->
        SyntaxVCT.B_finite_set num_list
and tsubst_tp
  bp5 tvar5 (SyntaxVCT.T_refined_type (zp, bp, cp)) =
    SyntaxVCT.T_refined_type (zp, tsubst_bp bp5 tvar5 bp, cp)
and tsubst_ctor_tau bp_5 tvar5 (ctor1, tp1) = (ctor1, tsubst_tp bp_5 tvar5 tp1)
and tsubst_ctor_tau_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, ctor_tau_XXX :: ctor_tau_list_XXX ->
        tsubst_ctor_tau bp_5 tvar5 ctor_tau_XXX ::
          tsubst_ctor_tau_list bp_5 tvar5 ctor_tau_list_XXX
and tsubst_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, bp_XXX :: bp_list_XXX ->
        tsubst_bp bp_5 tvar5 bp_XXX :: tsubst_bp_list bp_5 tvar5 bp_list_XXX
and tsubst_field_bp
  bp_5 tvar5 (field1, bp1) = (field1, tsubst_bp bp_5 tvar5 bp1)
and tsubst_field_bp_list
  bp_5 tvar5 x2 = match bp_5, tvar5, x2 with bp_5, tvar5, [] -> []
    | bp_5, tvar5, field_bp_XXX :: field_bp_list_XXX ->
        tsubst_field_bp bp_5 tvar5 field_bp_XXX ::
          tsubst_field_bp_list bp_5 tvar5 field_bp_list_XXX;;

let rec ce_subst_cep
  cep_5 zp5 x2 = match cep_5, zp5, x2 with
    cep_5, zp5, SyntaxVCT.CE_val vp -> SyntaxVCT.CE_val vp
    | cep_5, zp5, SyntaxVCT.CE_bop (bop, cep1, cep2) ->
        SyntaxVCT.CE_bop
          (bop, ce_subst_cep cep_5 zp5 cep1, ce_subst_cep cep_5 zp5 cep2)
    | cep_5, zp5, SyntaxVCT.CE_many_plus cep_list ->
        SyntaxVCT.CE_many_plus (ce_subst_cep_list cep_5 zp5 cep_list)
    | cep_5, zp5, SyntaxVCT.CE_uop (uop, cep) ->
        SyntaxVCT.CE_uop (uop, ce_subst_cep cep_5 zp5 cep)
    | cep_5, zp5, SyntaxVCT.CE_proj (p, cep) ->
        SyntaxVCT.CE_proj (p, ce_subst_cep cep_5 zp5 cep)
    | cep_5, zp5, SyntaxVCT.CE_field_access (xp, field) ->
        SyntaxVCT.CE_field_access (xp, field)
and ce_subst_cep_list
  cep_5 zp5 x2 = match cep_5, zp5, x2 with cep_5, zp5, [] -> []
    | cep_5, zp5, cep_XXX :: cep_list_XXX ->
        ce_subst_cep cep_5 zp5 cep_XXX ::
          ce_subst_cep_list cep_5 zp5 cep_list_XXX;;

let rec ce_subst_cp
  cep_5 zp5 x2 = match cep_5, zp5, x2 with
    cep_5, zp5, SyntaxVCT.C_true -> SyntaxVCT.C_true
    | cep_5, zp5, SyntaxVCT.C_false -> SyntaxVCT.C_false
    | cep_5, zp5, SyntaxVCT.C_conj (cp1, cp2) ->
        SyntaxVCT.C_conj (ce_subst_cp cep_5 zp5 cp1, ce_subst_cp cep_5 zp5 cp2)
    | cep_5, zp5, SyntaxVCT.C_conj_many cp_list ->
        SyntaxVCT.C_conj_many (ce_subst_cp_list cep_5 zp5 cp_list)
    | cep_5, zp5, SyntaxVCT.C_disj (cp1, cp2) ->
        SyntaxVCT.C_disj (ce_subst_cp cep_5 zp5 cp1, ce_subst_cp cep_5 zp5 cp2)
    | cep_5, zp5, SyntaxVCT.C_not cp ->
        SyntaxVCT.C_not (ce_subst_cp cep_5 zp5 cp)
    | cep_5, zp5, SyntaxVCT.C_eq (cep1, cep2) ->
        SyntaxVCT.C_eq
          (ce_subst_cep cep_5 zp5 cep1, ce_subst_cep cep_5 zp5 cep2)
    | cep_5, zp5, SyntaxVCT.C_leq (cep1, cep2) ->
        SyntaxVCT.C_leq
          (ce_subst_cep cep_5 zp5 cep1, ce_subst_cep cep_5 zp5 cep2)
    | cep_5, zp5, SyntaxVCT.C_imp (cp1, cp2) ->
        SyntaxVCT.C_imp (ce_subst_cp cep_5 zp5 cp1, ce_subst_cp cep_5 zp5 cp2)
and ce_subst_cp_list
  cep_5 zp5 x2 = match cep_5, zp5, x2 with cep_5, zp5, [] -> []
    | cep_5, zp5, cp_XXX :: cp_list_XXX ->
        ce_subst_cp cep_5 zp5 cp_XXX :: ce_subst_cp_list cep_5 zp5 cp_list_XXX;;

let rec ce_subst_bp
  cep5 zp5 x2 = match cep5, zp5, x2 with
    cep5, zp5, SyntaxVCT.B_var tvar -> SyntaxVCT.B_var tvar
    | cep5, zp5, SyntaxVCT.B_tid id -> SyntaxVCT.B_tid id
    | cep5, zp5, SyntaxVCT.B_int -> SyntaxVCT.B_int
    | cep5, zp5, SyntaxVCT.B_bool -> SyntaxVCT.B_bool
    | cep5, zp5, SyntaxVCT.B_bit -> SyntaxVCT.B_bit
    | cep5, zp5, SyntaxVCT.B_unit -> SyntaxVCT.B_unit
    | cep5, zp5, SyntaxVCT.B_real -> SyntaxVCT.B_real
    | cep5, zp5, SyntaxVCT.B_vec (order, bp) ->
        SyntaxVCT.B_vec (order, ce_subst_bp cep5 zp5 bp)
    | cep5, zp5, SyntaxVCT.B_list bp ->
        SyntaxVCT.B_list (ce_subst_bp cep5 zp5 bp)
    | cep5, zp5, SyntaxVCT.B_tuple bp_list ->
        SyntaxVCT.B_tuple (ce_subst_bp_list cep5 zp5 bp_list)
    | cep5, zp5, SyntaxVCT.B_union (id, ctor_tau_list) ->
        SyntaxVCT.B_union (id, ce_subst_ctor_tau_list cep5 zp5 ctor_tau_list)
    | cep5, zp5, SyntaxVCT.B_record field_bp_list ->
        SyntaxVCT.B_record (ce_subst_field_bp_list cep5 zp5 field_bp_list)
    | cep5, zp5, SyntaxVCT.B_undef -> SyntaxVCT.B_undef
    | cep5, zp5, SyntaxVCT.B_reg -> SyntaxVCT.B_reg
    | cep5, zp5, SyntaxVCT.B_string -> SyntaxVCT.B_string
    | cep5, zp5, SyntaxVCT.B_exception -> SyntaxVCT.B_exception
    | cep5, zp5, SyntaxVCT.B_finite_set num_list ->
        SyntaxVCT.B_finite_set num_list
and ce_subst_tp
  cep5 zp5 (SyntaxVCT.T_refined_type (zp, bp, cp)) =
    SyntaxVCT.T_refined_type
      (zp, ce_subst_bp cep5 zp5 bp, ce_subst_cp cep5 zp5 cp)
and ce_subst_ctor_tau cep5 zp5 (ctor1, tp1) = (ctor1, ce_subst_tp cep5 zp5 tp1)
and ce_subst_ctor_tau_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ctor_tau_XXX :: ctor_tau_list_XXX ->
        ce_subst_ctor_tau cep5 zp5 ctor_tau_XXX ::
          ce_subst_ctor_tau_list cep5 zp5 ctor_tau_list_XXX
and ce_subst_bp_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, bp_XXX :: bp_list_XXX ->
        ce_subst_bp cep5 zp5 bp_XXX :: ce_subst_bp_list cep5 zp5 bp_list_XXX
and ce_subst_field_bp
  cep5 zp5 (field1, bp1) = (field1, ce_subst_bp cep5 zp5 bp1)
and ce_subst_field_bp_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, field_bp_XXX :: field_bp_list_XXX ->
        ce_subst_field_bp cep5 zp5 field_bp_XXX ::
          ce_subst_field_bp_list cep5 zp5 field_bp_list_XXX;;

let rec ce_subst_patp
  cep5 zp5 x2 = match cep5, zp5, x2 with
    cep5, zp5, Pp_id (loc, id) -> Pp_id (loc, id)
    | cep5, zp5, Pp_wild loc -> Pp_wild loc
    | cep5, zp5, Pp_lit (loc, lit) -> Pp_lit (loc, lit)
    | cep5, zp5, Pp_typ (loc, tau, patp) ->
        Pp_typ (loc, ce_subst_tp cep5 zp5 tau, ce_subst_patp cep5 zp5 patp)
    | cep5, zp5, Pp_app (loc, id, patp_list) ->
        Pp_app (loc, id, ce_subst_patp_list_Pp_app cep5 zp5 patp_list)
    | cep5, zp5, Pp_tup (loc, patp_list) ->
        Pp_tup (loc, ce_subst_patp_list_Pp_tup cep5 zp5 patp_list)
    | cep5, zp5, Pp_vector_concat (loc, patp_list) ->
        Pp_vector_concat
          (loc, ce_subst_patp_list_Pp_vector_concat cep5 zp5 patp_list)
    | cep5, zp5, Pp_as_var (loc, patp, xp) ->
        Pp_as_var (loc, ce_subst_patp cep5 zp5 patp, xp)
    | cep5, zp5, Pp_as_typ (loc, patp, tau) ->
        Pp_as_typ (loc, ce_subst_patp cep5 zp5 patp, ce_subst_tp cep5 zp5 tau)
    | cep5, zp5, Pp_cons (loc, patp1, patp2) ->
        Pp_cons
          (loc, ce_subst_patp cep5 zp5 patp1, ce_subst_patp cep5 zp5 patp2)
    | cep5, zp5, Pp_string_append (loc, patp_list) ->
        Pp_string_append
          (loc, ce_subst_patp_list_Pp_string_append cep5 zp5 patp_list)
    | cep5, zp5, Pp_vector (loc, patp_list) ->
        Pp_vector (loc, ce_subst_patp_list_Pp_vector cep5 zp5 patp_list)
    | cep5, zp5, Pp_list (loc, patp_list) ->
        Pp_list (loc, ce_subst_patp_list_Pp_list cep5 zp5 patp_list)
    | cep5, zp5, Pp_record (loc, field_patp_list) ->
        Pp_record
          (loc, ce_subst_field_patp_list_Pp_record cep5 zp5 field_patp_list)
and ce_subst_patp_list_Pp_app
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_app cep5 zp5 patp_list_XXX
and ce_subst_patp_list_Pp_tup
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_tup cep5 zp5 patp_list_XXX
and ce_subst_patp_list_Pp_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_list cep5 zp5 patp_list_XXX
and ce_subst_patp_list_Pp_vector
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_vector cep5 zp5 patp_list_XXX
and ce_subst_field_patp_Pp_record
  cep5 zp5 (field1, patp1) = (field1, ce_subst_patp cep5 zp5 patp1)
and ce_subst_field_patp_list_Pp_record
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, field_patp_XXX :: field_patp_list_XXX ->
        ce_subst_field_patp_Pp_record cep5 zp5 field_patp_XXX ::
          ce_subst_field_patp_list_Pp_record cep5 zp5 field_patp_list_XXX
and ce_subst_patp_list_Pp_string_append
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_string_append cep5 zp5 patp_list_XXX
and ce_subst_patp_list_Pp_vector_concat
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, patp_XXX :: patp_list_XXX ->
        ce_subst_patp cep5 zp5 patp_XXX ::
          ce_subst_patp_list_Pp_vector_concat cep5 zp5 patp_list_XXX;;

let rec ce_subst_lexpp
  cep5 zp5 x2 = match cep5, zp5, x2 with
    cep5, zp5, LEXPp_mvar (loc, up) -> LEXPp_mvar (loc, up)
    | cep5, zp5, LEXPp_cast (loc, tau, up) ->
        LEXPp_cast (loc, ce_subst_tp cep5 zp5 tau, up)
    | cep5, zp5, LEXPp_tup (loc, lexpp_list) ->
        LEXPp_tup (loc, ce_subst_lexpp_list cep5 zp5 lexpp_list)
    | cep5, zp5, LEXPp_field (loc, lexpp, id) ->
        LEXPp_field (loc, ce_subst_lexpp cep5 zp5 lexpp, id)
and ce_subst_lexpp_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, lexpp_XXX :: lexpp_list_XXX ->
        ce_subst_lexpp cep5 zp5 lexpp_XXX ::
          ce_subst_lexpp_list cep5 zp5 lexpp_list_XXX;;

let rec ce_subst_ep
  cep5 zp5 x2 = match cep5, zp5, x2 with
    cep5, zp5, Ep_val (loc, vp) -> Ep_val (loc, vp)
    | cep5, zp5, Ep_mvar (loc, up) -> Ep_mvar (loc, up)
    | cep5, zp5, Ep_concat (loc, ep_list) ->
        Ep_concat (loc, ce_subst_ep_list_Ep_concat cep5 zp5 ep_list)
    | cep5, zp5, Ep_tuple (loc, ep_list) ->
        Ep_tuple (loc, ce_subst_ep_list_Ep_tuple cep5 zp5 ep_list)
    | cep5, zp5, Ep_app (loc, fp, ep) ->
        Ep_app (loc, fp, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_bop (loc, bop, ep1, ep2) ->
        Ep_bop (loc, bop, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2)
    | cep5, zp5, Ep_uop (loc, uop, ep) ->
        Ep_uop (loc, uop, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_proj (loc, p, ep) ->
        Ep_proj (loc, p, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_constr (loc, ctor, ep) ->
        Ep_constr (loc, ctor, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_field_access (loc, ep, field) ->
        Ep_field_access (loc, ce_subst_ep cep5 zp5 ep, field)
    | cep5, zp5, Ep_sizeof (loc, cep) ->
        Ep_sizeof (loc, ce_subst_cep cep5 zp5 cep)
    | cep5, zp5, Ep_cast (loc, tau, ep) ->
        Ep_cast (loc, ce_subst_tp cep5 zp5 tau, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_record (loc, field_ep_list) ->
        Ep_record (loc, ce_subst_field_ep_list_Ep_record cep5 zp5 field_ep_list)
    | cep5, zp5, Ep_record_update (loc, ep, field_ep_list) ->
        Ep_record_update
          (loc, ce_subst_ep cep5 zp5 ep,
            ce_subst_field_ep_list_Ep_record_update cep5 zp5 field_ep_list)
    | cep5, zp5, Ep_let (loc, letbind, ep2) ->
        Ep_let
          (loc, ce_subst_letbind cep5 zp5 letbind, ce_subst_ep cep5 zp5 ep2)
    | cep5, zp5, Ep_let2 (loc, xp, tau, ep1, ep2) ->
        Ep_let2
          (loc, xp, ce_subst_tp cep5 zp5 tau, ce_subst_ep cep5 zp5 ep1,
            (if Lista.member SyntaxVCT.equal_xp [xp] zp5 then ep2
              else ce_subst_ep cep5 zp5 ep2))
    | cep5, zp5, Ep_if (loc, ep1, ep2, ep3) ->
        Ep_if (loc, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2,
                ce_subst_ep cep5 zp5 ep3)
    | cep5, zp5, Ep_block (loc, ep_list) ->
        Ep_block (loc, ce_subst_ep_list_Ep_block cep5 zp5 ep_list)
    | cep5, zp5, Ep_case (loc, ep, pexpp_list) ->
        Ep_case
          (loc, ce_subst_ep cep5 zp5 ep,
            ce_subst_pexpp_list_Ep_case cep5 zp5 pexpp_list)
    | cep5, zp5, Ep_assign (loc, lexpp, ep1, ep2) ->
        Ep_assign
          (loc, ce_subst_lexpp cep5 zp5 lexpp, ce_subst_ep cep5 zp5 ep1,
            ce_subst_ep cep5 zp5 ep2)
    | cep5, zp5, Ep_exit (loc, ep) -> Ep_exit (loc, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_return (loc, ep) -> Ep_return (loc, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_throw (loc, ep) -> Ep_throw (loc, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_try (loc, ep, pexpp_list) ->
        Ep_try
          (loc, ce_subst_ep cep5 zp5 ep,
            ce_subst_pexpp_list_Ep_try cep5 zp5 pexpp_list)
    | cep5, zp5, Ep_constraint (loc, cp) ->
        Ep_constraint (loc, ce_subst_cp cep5 zp5 cp)
    | cep5, zp5, Ep_loop (loc, loop, ep1, ep2) ->
        Ep_loop (loc, loop, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2)
    | cep5, zp5, Ep_for (loc, id, ep1, ep2, ep3, order, ep4) ->
        Ep_for
          (loc, id, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2,
            ce_subst_ep cep5 zp5 ep3, order, ce_subst_ep cep5 zp5 ep4)
    | cep5, zp5, Ep_assert (loc, ep1, ep2) ->
        Ep_assert (loc, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2)
    | cep5, zp5, Ep_vec (loc, ep_list) ->
        Ep_vec (loc, ce_subst_ep_list_Ep_vec cep5 zp5 ep_list)
    | cep5, zp5, Ep_list (loc, ep_list) ->
        Ep_list (loc, ce_subst_ep_list_Ep_list cep5 zp5 ep_list)
    | cep5, zp5, Ep_cons (loc, ep1, ep2) ->
        Ep_cons (loc, ce_subst_ep cep5 zp5 ep1, ce_subst_ep cep5 zp5 ep2)
and ce_subst_pexpp
  cep5 zp5 x2 = match cep5, zp5, x2 with
    cep5, zp5, PEXPp_exp (patp, ep) ->
      PEXPp_exp (ce_subst_patp cep5 zp5 patp, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, PEXPp_when (patp, ep1, ep2) ->
        PEXPp_when
          (ce_subst_patp cep5 zp5 patp, ce_subst_ep cep5 zp5 ep1,
            ce_subst_ep cep5 zp5 ep2)
and ce_subst_pexpp_list_Ep_try
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, pexpp_XXX :: pexpp_list_XXX ->
        ce_subst_pexpp cep5 zp5 pexpp_XXX ::
          ce_subst_pexpp_list_Ep_try cep5 zp5 pexpp_list_XXX
and ce_subst_pexpp_list_Ep_case
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, pexpp_XXX :: pexpp_list_XXX ->
        ce_subst_pexpp cep5 zp5 pexpp_XXX ::
          ce_subst_pexpp_list_Ep_case cep5 zp5 pexpp_list_XXX
and ce_subst_letbind
  cep5 zp5 (LBp_val (loc, patp, ep)) =
    LBp_val (loc, ce_subst_patp cep5 zp5 patp, ce_subst_ep cep5 zp5 ep)
and ce_subst_ep_list_Ep_vec
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ep_XXX :: ep_list_XXX ->
        ce_subst_ep cep5 zp5 ep_XXX ::
          ce_subst_ep_list_Ep_vec cep5 zp5 ep_list_XXX
and ce_subst_ep_list_Ep_list
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ep_XXX :: ep_list_XXX ->
        ce_subst_ep cep5 zp5 ep_XXX ::
          ce_subst_ep_list_Ep_list cep5 zp5 ep_list_XXX
and ce_subst_ep_list_Ep_block
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ep_XXX :: ep_list_XXX ->
        ce_subst_ep cep5 zp5 ep_XXX ::
          ce_subst_ep_list_Ep_block cep5 zp5 ep_list_XXX
and ce_subst_ep_list_Ep_tuple
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ep_XXX :: ep_list_XXX ->
        ce_subst_ep cep5 zp5 ep_XXX ::
          ce_subst_ep_list_Ep_tuple cep5 zp5 ep_list_XXX
and ce_subst_ep_list_Ep_concat
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, ep_XXX :: ep_list_XXX ->
        ce_subst_ep cep5 zp5 ep_XXX ::
          ce_subst_ep_list_Ep_concat cep5 zp5 ep_list_XXX
and ce_subst_field_ep_Ep_record
  cep5 zp5 (field1, ep1) = (field1, ce_subst_ep cep5 zp5 ep1)
and ce_subst_field_ep_list_Ep_record
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, field_ep_XXX :: field_ep_list_XXX ->
        ce_subst_field_ep_Ep_record cep5 zp5 field_ep_XXX ::
          ce_subst_field_ep_list_Ep_record cep5 zp5 field_ep_list_XXX
and ce_subst_field_ep_Ep_record_update
  cep5 zp5 (field1, ep1) = (field1, ce_subst_ep cep5 zp5 ep1)
and ce_subst_field_ep_list_Ep_record_update
  cep5 zp5 x2 = match cep5, zp5, x2 with cep5, zp5, [] -> []
    | cep5, zp5, field_ep_XXX :: field_ep_list_XXX ->
        ce_subst_field_ep_Ep_record_update cep5 zp5 field_ep_XXX ::
          ce_subst_field_ep_list_Ep_record_update cep5 zp5 field_ep_list_XXX;;

let rec ce_subst_funclp
  cep5 zp5 (FCLp_funcl (loc, id, pexpp)) =
    FCLp_funcl (loc, id, ce_subst_pexpp cep5 zp5 pexpp);;

end;; (*struct SyntaxPED*)

module Monad : sig
  type tag = IfThen | IfElse
  type witness = LitI | VarI | TrueI | FalseI | NumI | TupleI |
    PlusI of witness * witness | LEqI of witness * witness | AppI of witness |
    CValI of witness * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * SyntaxVCT.cp
    | CLetI of witness * witness | CLet2I of witness * witness |
    CIfI of witness * witness * witness
  type state = StateD of Arith.int * witness list
  type fail_reason = VarUnknown of Location.loc * SyntaxVCT.xp |
    OperandTypesWrongLeft of SyntaxPED.ep * SyntaxVCT.bp * SyntaxVCT.bp |
    OperandTypesWrongRight of SyntaxPED.ep * SyntaxVCT.bp * SyntaxVCT.bp |
    CheckFail of
      Location.loc * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * string *
        SyntaxVCT.tau * SyntaxVCT.tau
    | IfCondType of Location.loc * SyntaxVCT.tau |
    IfThenBranchType of Location.loc | IfElseBranchType of Location.loc |
    NotSatisfiable | FunctionUnknown of SyntaxPED.ep * SyntaxVCT.xp |
    FunctionType |
    FunctionArgWrongType of Location.loc * SyntaxVCT.tau * SyntaxVCT.tau |
    VectorElementsDiffType | UnknownConstructor of Location.loc * string |
    NotImplemented of Location.loc * string | UnknownError |
    UnknownErrorLoc of Location.loc | TypeError of Location.loc * string |
    RecordFieldUpdateFail of Location.loc * string |
    ScopeError of
      Location.loc * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * SyntaxVCT.xp
  type 'a checkD = Check_Ok of 'a | Check_Fail of tag option * fail_reason
  type 'a checkM = State of (state -> 'a checkD * state)
  val fail : fail_reason -> 'a checkM
  val run_state : 'a checkM -> state -> 'a checkD * state
  val check_bind : 'a checkM -> ('a -> 'b checkM) -> 'b checkM
  val return : 'a -> 'a checkM
  val mapM : ('a -> 'b checkM) -> 'a list -> ('b list) checkM
  val trace : witness -> unit checkM
  val map2iM :
    ('a -> 'b -> Arith.nat -> 'c checkM) ->
      'a list -> 'b list -> ('c list) checkM
  val mk_var : SyntaxVCT.xp -> SyntaxVCT.vp
  val mk_fresh : Stringa.char list -> SyntaxVCT.xp checkM
  val subst_c_list2 :
    SyntaxVCT.cp -> (SyntaxVCT.xp * SyntaxVCT.vp) list -> SyntaxVCT.cp
  val freshen_vars :
    (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
      ((SyntaxVCT.xp * SyntaxVCT.vp) list *
        (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list)
        checkM
  val freshen_t : SyntaxVCT.tau -> SyntaxVCT.tau checkM
  val lookup_fun :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        SyntaxVCT.xp ->
          ((SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list) option
  val convert_fun :
    SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option) ->
      (SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) checkM
  val lookup_fun_and_convert_aux :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        SyntaxVCT.xp ->
          ((SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list) checkM
end = struct

type tag = IfThen | IfElse;;

type witness = LitI | VarI | TrueI | FalseI | NumI | TupleI |
  PlusI of witness * witness | LEqI of witness * witness | AppI of witness |
  CValI of witness * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * SyntaxVCT.cp |
  CLetI of witness * witness | CLet2I of witness * witness |
  CIfI of witness * witness * witness;;

type state = StateD of Arith.int * witness list;;

type fail_reason = VarUnknown of Location.loc * SyntaxVCT.xp |
  OperandTypesWrongLeft of SyntaxPED.ep * SyntaxVCT.bp * SyntaxVCT.bp |
  OperandTypesWrongRight of SyntaxPED.ep * SyntaxVCT.bp * SyntaxVCT.bp |
  CheckFail of
    Location.loc * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * string *
      SyntaxVCT.tau * SyntaxVCT.tau
  | IfCondType of Location.loc * SyntaxVCT.tau |
  IfThenBranchType of Location.loc | IfElseBranchType of Location.loc |
  NotSatisfiable | FunctionUnknown of SyntaxPED.ep * SyntaxVCT.xp | FunctionType
  | FunctionArgWrongType of Location.loc * SyntaxVCT.tau * SyntaxVCT.tau |
  VectorElementsDiffType | UnknownConstructor of Location.loc * string |
  NotImplemented of Location.loc * string | UnknownError |
  UnknownErrorLoc of Location.loc | TypeError of Location.loc * string |
  RecordFieldUpdateFail of Location.loc * string |
  ScopeError of
    Location.loc * (SyntaxPED.pexpp, unit) Contexts.gamma_ext * SyntaxVCT.xp;;

type 'a checkD = Check_Ok of 'a | Check_Fail of tag option * fail_reason;;

type 'a checkM = State of (state -> 'a checkD * state);;

let rec fail r = State (fun a -> (Check_Fail (None, r), a));;

let rec run_state (State x) = x;;

let rec check_bind
  x f = State (fun s ->
                (match run_state x s with (Check_Ok y, sa) -> run_state (f y) sa
                  | (Check_Fail (t, r), sa) -> (Check_Fail (t, r), sa)));;

let rec return x = State (fun a -> (Check_Ok x, a));;

let rec mapM
  uu x1 = match uu, x1 with uu, [] -> return []
    | f, x :: xs ->
        check_bind (f x)
          (fun xa -> check_bind (mapM f xs) (fun xsa -> return (xa :: xsa)));;

let rec trace
  w = State (fun (StateD (i, ws)) -> (Check_Ok (), StateD (i, w :: ws)));;

let rec map2iM
  uu x1 uv = match uu, x1, uv with uu, [], uv -> return []
    | uw, v :: va, [] -> return []
    | f, x :: xs, y :: ys ->
        check_bind (f x y (Arith.plus_nat (Lista.size_list xs) Arith.one_nat))
          (fun xy ->
            check_bind (map2iM f xs ys) (fun xys -> return (xy :: xys)));;

let rec mk_var x = SyntaxVCT.V_var x;;

let rec mk_fresh
  prefix =
    State (fun (StateD (i, w)) ->
            (Check_Ok
               (SyntaxVCT.VNamed
                 (Stringa.implode prefix ^ Utils.string_lit_of_int i)),
              StateD (Arith.plus_int i Arith.one_int, w)));;

let rec subst_c_list2
  c x1 = match c, x1 with c, [] -> c
    | c, (x, v) :: xvs -> subst_c_list2 (SyntaxPED.subst_cp v x c) xvs;;

let rec freshen_vars
  = function [] -> return ([], [])
    | (x, (b, c)) :: xbc ->
        check_bind
          (mk_fresh
            [Stringa.Chara (true, true, false, true, false, true, true, false)])
          (fun xa ->
            check_bind (freshen_vars xbc)
              (fun (x1, x2) ->
                return
                  ((x, mk_var xa) :: x1,
                    (xa, (b, SyntaxPED.subst_cp (mk_var xa) x c)) :: x2)));;

let rec freshen_t
  (SyntaxVCT.T_refined_type (z, b, c)) =
    check_bind (freshen_vars [])
      (fun (kmap, kvars) ->
        (let _ =
           Lista.map (fun (x, (ba, ca)) -> (x, (ba, subst_c_list2 ca kmap)))
             kvars
           in
          return
            (SyntaxVCT.T_refined_type
              (SyntaxVCT.VIndex, b, subst_c_list2 c kmap))));;

let rec lookup_fun
  theta gamma x2 = match theta, gamma, x2 with
    theta, gamma, SyntaxVCT.VNamed cn ->
      (match ContextsPiDelta.lookup_fun_aux gamma (SyntaxVCT.VNamed cn)
        with None ->
          (match ContextsPiDelta.lookup_constr_union theta cn with None -> None
            | Some ret ->
              (match ContextsPiDelta.lookup_constr_in_type ret cn
                with None -> None
                | Some (SyntaxVCT.T_refined_type (z, b, c)) ->
                  Some [(SyntaxVCT.VNamed cn,
                          (SyntaxVCT.A_function
                             (SyntaxVCT.VNamed "_x", b,
                               SyntaxPED.subst_cp
                                 (SyntaxVCT.V_var (SyntaxVCT.VNamed "_x")) z c,
                               ret),
                            Some (SyntaxPED.PEXPp_exp
                                   (SyntaxPED.Pp_id
                                      (Location.Loc_unknown, "_x"),
                                     SyntaxPED.Ep_val
                                       (Location.Loc_unknown,
 SyntaxVCT.V_constr (cn, SyntaxVCT.V_var (SyntaxVCT.VNamed "_x")))))))]))
        | Some a -> Some a)
    | uu, uv, SyntaxVCT.VIndex -> None;;

let rec convert_fun
  (SyntaxVCT.VNamed f,
    (SyntaxVCT.A_function (SyntaxVCT.VNamed xin, bin, cin, t2), s))
    = check_bind
        (mk_fresh
          ([Stringa.Chara (true, true, true, true, true, false, true, false);
             Stringa.Chara (false, false, false, true, true, true, true, false);
             Stringa.Chara (true, false, false, true, false, true, true, false);
             Stringa.Chara (false, true, true, true, false, true, true, false);
             Stringa.Chara (true, true, true, true, true, false, true, false)] @
            Stringa.explode f))
        (fun xina ->
          check_bind
            (match s with None -> return None
              | Some sa ->
                return
                  (Some (SyntaxPED.subst_pexpp (SyntaxVCT.V_var xina)
                          (SyntaxVCT.VNamed xin) sa)))
            (fun sa ->
              return
                (SyntaxVCT.VNamed f,
                  (SyntaxVCT.A_function
                     (xina, bin,
                       SyntaxPED.subst_cp (SyntaxVCT.V_var xina)
                         (SyntaxVCT.VNamed xin) cin,
                       SyntaxPED.subst_tp (SyntaxVCT.V_var xina)
                         (SyntaxVCT.VNamed xin) t2),
                    sa))));;

let rec lookup_fun_and_convert_aux
  t pi f =
    (match lookup_fun t pi f with None -> return []
      | Some a -> mapM convert_fun a);;

end;; (*struct Monad*)

module Option : sig
  val equal_optiona : 'a HOL.equal -> 'a option -> 'a option -> bool
  val equal_option : 'a HOL.equal -> ('a option) HOL.equal
end = struct

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> HOL.eq _A x2 y2
                           | None, None -> true;;

let rec equal_option _A =
  ({HOL.equal = equal_optiona _A} : ('a option) HOL.equal);;

end;; (*struct Option*)
