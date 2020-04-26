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

module Product_Type : sig
  val equal_boola : bool -> bool -> bool
  val equal_bool : bool HOL.equal
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit HOL.equal
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

let rec equal_boola p pa = match p, pa with p, true -> p
                      | p, false -> not p
                      | true, p -> p
                      | false, p -> not p;;

let equal_bool = ({HOL.equal = equal_boola} : bool HOL.equal);;

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

let rec equal_unita u v = true;;

let equal_unit = ({HOL.equal = equal_unita} : unit HOL.equal);;

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

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
  type int = Int_of_integer of Z.t
  type num = One | Bit0 of num | Bit1 of num
  val one_inta : int
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_int : int one
  val integer_of_int : int -> Z.t
  val times_inta : int -> int -> int
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power = {one_power : 'a one; times_power : 'a times}
  val times_int : int times
  val power_int : int power
  val equal_integer : Z.t HOL.equal
  val one_integera : Z.t
  val one_integer : Z.t one
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val zero_integer : Z.t zero
  val ord_integer : Z.t Orderings.ord
  type 'a zero_neq_one =
    {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero}
  val zero_neq_one_integer : Z.t zero_neq_one
  type nat = Nat of Z.t
  val nat : int -> nat
  val integer_of_nat : nat -> Z.t
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val suc : nat -> nat
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val power : 'a power -> 'a -> nat -> 'a
  val less_int : int -> int -> bool
  val less_nat : nat -> nat -> bool
  val int_of_nat : nat -> int
  val plus_int : int -> int -> int
  val zero_int : int
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val nat_of_integer : Z.t -> nat
  val bit_cut_integer : Z.t -> Z.t * bool
  val minus_int : int -> int -> int
  val less_eq_nat : nat -> nat -> bool
  val uminus_int : int -> int
  val of_bool : 'a zero_neq_one -> bool -> 'a
  val divide_integer : Z.t -> Z.t -> Z.t
  val divide_nat : nat -> nat -> nat
  val modulo_integer : Z.t -> Z.t -> Z.t
  val modulo_nat : nat -> nat -> nat
end = struct

type int = Int_of_integer of Z.t;;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec integer_of_int (Int_of_integer k) = k;;

let rec times_inta
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_int = ({times = times_inta} : int times);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let equal_integer = ({HOL.equal = Z.equal} : Z.t HOL.equal);;

let one_integera : Z.t = (Z.of_int 1);;

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

type nat = Nat of Z.t;;

let rec nat k = Nat (Orderings.max ord_integer Z.zero (integer_of_int k));;

let rec integer_of_nat (Nat x) = x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec minus_nat
  m n = Nat (Orderings.max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let zero_nat : nat = Nat Z.zero;;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nat)));;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec plus_int
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

let zero_int : int = Int_of_integer Z.zero;;

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
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val nth : 'a list -> Arith.nat -> 'a
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val upto_aux : Arith.int -> Arith.int -> Arith.int list -> Arith.int list
  val upto : Arith.int -> Arith.int -> Arith.int list
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val hd : 'a list -> 'a
  val remdups : 'a HOL.equal -> 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val enumerate : Arith.nat -> 'a list -> (Arith.nat * 'a) list
  val removeAll : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val replicate : Arith.nat -> 'a -> 'a list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val list_update : 'a list -> Arith.nat -> 'a -> 'a list
  val list_all : ('a -> bool) -> 'a list -> bool
  val size_list : 'a list -> Arith.nat
end = struct

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({HOL.equal = equal_lista _A} : ('a list) HOL.equal);;

let rec nth
  (x :: xs) n =
    (if Arith.equal_nat n Arith.zero_nat then x
      else nth xs (Arith.minus_nat n Arith.one_nat));;

let rec upt
  i j = (if Arith.less_nat i j then i :: upt (Arith.suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec upto_aux
  i j js =
    (if Arith.less_int j i then js
      else upto_aux i (Arith.minus_int j Arith.one_inta) (j :: js));;

let rec upto i j = upto_aux i j [];;

let rec foldr f x1 = match f, x1 with f, [] -> Fun.id
                | f, x :: xs -> Fun.comp (f x) (foldr f xs);;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> HOL.eq _A x y || member _A xs y;;

let rec insert _A x xs = (if member _A xs x then xs else x :: xs);;

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

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if HOL.eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec replicate
  n x = (if Arith.equal_nat n Arith.zero_nat then []
          else x :: replicate (Arith.minus_nat n Arith.one_nat) x);;

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

end;; (*struct Lista*)

module Z3 : sig
  type z3_expr = Z3E_num of Z.t | Z3E_var of string | Z3E_true | Z3E_false |
    Z3E_unit | Z3E_bitone | Z3E_bitzero | Z3E_len of z3_expr |
    Z3E_leq of z3_expr * z3_expr | Z3E_geq of z3_expr * z3_expr |
    Z3E_plus of z3_expr * z3_expr | Z3E_times of z3_expr * z3_expr |
    Z3E_div of z3_expr * z3_expr | Z3E_mod of z3_expr * z3_expr |
    Z3E_minus of z3_expr * z3_expr | Z3E_eq of z3_expr * z3_expr |
    Z3E_not of z3_expr | Z3E_exp of z3_expr | Z3E_abs of z3_expr |
    Z3E_and of z3_expr * z3_expr | Z3E_or of z3_expr * z3_expr |
    Z3E_neq of z3_expr * z3_expr | Z3E_bitvec of string |
    Z3E_constr of string * z3_expr list | Z3E_concat of z3_expr list |
    Z3E_proj of string * z3_expr | Z3E_string of string
  val equal_z3_expr : z3_expr HOL.equal
  val equal_z3_expra : z3_expr -> z3_expr -> bool
  type z3_bool_expr = Z3BE_true | Z3BE_false | Z3BE_not of z3_bool_expr |
    Z3BE_and of z3_bool_expr list | Z3BE_or of z3_bool_expr list |
    Z3BE_eq of z3_expr * z3_expr | Z3BE_leq of z3_expr * z3_expr |
    Z3BE_implies of z3_bool_expr * z3_bool_expr |
    Z3BE_pred of string * z3_expr list
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
  Z3E_not of z3_expr | Z3E_exp of z3_expr | Z3E_abs of z3_expr |
  Z3E_and of z3_expr * z3_expr | Z3E_or of z3_expr * z3_expr |
  Z3E_neq of z3_expr * z3_expr | Z3E_bitvec of string |
  Z3E_constr of string * z3_expr list | Z3E_concat of z3_expr list |
  Z3E_proj of string * z3_expr | Z3E_string of string;;

let rec equal_z3_expr () = ({HOL.equal = equal_z3_expra} : z3_expr HOL.equal)
and equal_z3_expra
  x0 x1 = match x0, x1 with Z3E_proj (x261, x262), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_proj (x261, x262) -> false
    | Z3E_concat x25, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_concat x25 -> false
    | Z3E_constr (x241, x242), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_constr (x241, x242) -> false
    | Z3E_bitvec x23, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_bitvec x23 -> false
    | Z3E_neq (x221, x222), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_neq (x221, x222) -> false
    | Z3E_or (x211, x212), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_or (x211, x212) -> false
    | Z3E_and (x201, x202), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_and (x201, x202) -> false
    | Z3E_abs x19, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_abs x19 -> false
    | Z3E_exp x18, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_exp x18 -> false
    | Z3E_not x17, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_not x17 -> false
    | Z3E_not x17, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_not x17 -> false
    | Z3E_eq (x161, x162), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_eq (x161, x162) -> false
    | Z3E_minus (x151, x152), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_minus (x151, x152) -> false
    | Z3E_mod (x141, x142), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_mod (x141, x142) -> false
    | Z3E_div (x131, x132), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_not x17 -> false
    | Z3E_not x17, Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_eq (x161, x162) -> false
    | Z3E_eq (x161, x162), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_minus (x151, x152) -> false
    | Z3E_minus (x151, x152), Z3E_div (x131, x132) -> false
    | Z3E_div (x131, x132), Z3E_mod (x141, x142) -> false
    | Z3E_mod (x141, x142), Z3E_div (x131, x132) -> false
    | Z3E_times (x121, x122), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_times (x121, x122) -> false
    | Z3E_times (x121, x122), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_times (x121, x122) -> false
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
    | Z3E_plus (x111, x112), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_plus (x111, x112) -> false
    | Z3E_plus (x111, x112), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_plus (x111, x112) -> false
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
    | Z3E_geq (x101, x102), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_geq (x101, x102) -> false
    | Z3E_geq (x101, x102), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_geq (x101, x102) -> false
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
    | Z3E_leq (x91, x92), Z3E_string x27 -> false
    | Z3E_string x27, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_leq (x91, x92) -> false
    | Z3E_leq (x91, x92), Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_leq (x91, x92) -> false
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
    | Z3E_len x8, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_len x8 -> false
    | Z3E_len x8, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_len x8 -> false
    | Z3E_len x8, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_len x8 -> false
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
    | Z3E_bitzero, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_bitzero -> false
    | Z3E_bitzero, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_bitzero -> false
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
    | Z3E_bitone, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_bitone -> false
    | Z3E_bitone, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_bitone -> false
    | Z3E_bitone, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_bitone -> false
    | Z3E_bitone, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_bitone -> false
    | Z3E_bitone, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_bitone -> false
    | Z3E_bitone, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_bitone -> false
    | Z3E_bitone, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_bitone -> false
    | Z3E_bitone, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_bitone -> false
    | Z3E_bitone, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_bitone -> false
    | Z3E_bitone, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_bitone -> false
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
    | Z3E_unit, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_unit -> false
    | Z3E_unit, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_unit -> false
    | Z3E_unit, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_unit -> false
    | Z3E_unit, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_unit -> false
    | Z3E_unit, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_unit -> false
    | Z3E_unit, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_unit -> false
    | Z3E_unit, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_unit -> false
    | Z3E_unit, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_unit -> false
    | Z3E_unit, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_unit -> false
    | Z3E_unit, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_unit -> false
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
    | Z3E_false, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_false -> false
    | Z3E_false, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_false -> false
    | Z3E_false, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_false -> false
    | Z3E_false, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_false -> false
    | Z3E_false, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_false -> false
    | Z3E_false, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_false -> false
    | Z3E_false, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_false -> false
    | Z3E_false, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_false -> false
    | Z3E_false, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_false -> false
    | Z3E_false, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_false -> false
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
    | Z3E_true, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_true -> false
    | Z3E_true, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_true -> false
    | Z3E_true, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_true -> false
    | Z3E_true, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_true -> false
    | Z3E_true, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_true -> false
    | Z3E_true, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_true -> false
    | Z3E_true, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_true -> false
    | Z3E_true, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_true -> false
    | Z3E_true, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_true -> false
    | Z3E_true, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_true -> false
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
    | Z3E_var x2, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_var x2 -> false
    | Z3E_var x2, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_var x2 -> false
    | Z3E_var x2, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_var x2 -> false
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
    | Z3E_num x1, Z3E_string x27 -> false
    | Z3E_string x27, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_proj (x261, x262) -> false
    | Z3E_proj (x261, x262), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_concat x25 -> false
    | Z3E_concat x25, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_constr (x241, x242) -> false
    | Z3E_constr (x241, x242), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_bitvec x23 -> false
    | Z3E_bitvec x23, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_neq (x221, x222) -> false
    | Z3E_neq (x221, x222), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_or (x211, x212) -> false
    | Z3E_or (x211, x212), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_and (x201, x202) -> false
    | Z3E_and (x201, x202), Z3E_num x1 -> false
    | Z3E_num x1, Z3E_abs x19 -> false
    | Z3E_abs x19, Z3E_num x1 -> false
    | Z3E_num x1, Z3E_exp x18 -> false
    | Z3E_exp x18, Z3E_num x1 -> false
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
    | Z3E_string x27, Z3E_string y27 -> ((x27 : string) = y27)
    | Z3E_proj (x261, x262), Z3E_proj (y261, y262) ->
        ((x261 : string) = y261) && equal_z3_expra x262 y262
    | Z3E_concat x25, Z3E_concat y25 ->
        Lista.equal_lista (equal_z3_expr ()) x25 y25
    | Z3E_constr (x241, x242), Z3E_constr (y241, y242) ->
        ((x241 : string) = y241) &&
          Lista.equal_lista (equal_z3_expr ()) x242 y242
    | Z3E_bitvec x23, Z3E_bitvec y23 -> ((x23 : string) = y23)
    | Z3E_neq (x221, x222), Z3E_neq (y221, y222) ->
        equal_z3_expra x221 y221 && equal_z3_expra x222 y222
    | Z3E_or (x211, x212), Z3E_or (y211, y212) ->
        equal_z3_expra x211 y211 && equal_z3_expra x212 y212
    | Z3E_and (x201, x202), Z3E_and (y201, y202) ->
        equal_z3_expra x201 y201 && equal_z3_expra x202 y202
    | Z3E_abs x19, Z3E_abs y19 -> equal_z3_expra x19 y19
    | Z3E_exp x18, Z3E_exp y18 -> equal_z3_expra x18 y18
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
  Z3BE_implies of z3_bool_expr * z3_bool_expr |
  Z3BE_pred of string * z3_expr list;;

let rec equal_z3_bool_expr () =
  ({HOL.equal = equal_z3_bool_expra} : z3_bool_expr HOL.equal)
and equal_z3_bool_expra
  x0 x1 = match x0, x1 with
    Z3BE_implies (x81, x82), Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_implies (x81, x82) -> false
    | Z3BE_leq (x71, x72), Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_leq (x71, x72) -> false
    | Z3BE_eq (x61, x62), Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_eq (x61, x62) -> false
    | Z3BE_or x5, Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_or x5 -> false
    | Z3BE_and x4, Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_implies (x81, x82) -> false
    | Z3BE_implies (x81, x82), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_leq (x71, x72) -> false
    | Z3BE_leq (x71, x72), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_eq (x61, x62) -> false
    | Z3BE_eq (x61, x62), Z3BE_and x4 -> false
    | Z3BE_and x4, Z3BE_or x5 -> false
    | Z3BE_or x5, Z3BE_and x4 -> false
    | Z3BE_not x3, Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_not x3 -> false
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
    | Z3BE_false, Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_false -> false
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
    | Z3BE_true, Z3BE_pred (x91, x92) -> false
    | Z3BE_pred (x91, x92), Z3BE_true -> false
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
    | Z3BE_pred (x91, x92), Z3BE_pred (y91, y92) ->
        ((x91 : string) = y91) && Lista.equal_lista equal_z3_expr x92 y92
    | Z3BE_implies (x81, x82), Z3BE_implies (y81, y82) ->
        equal_z3_bool_expra x81 y81 && equal_z3_bool_expra x82 y82
    | Z3BE_leq (x71, x72), Z3BE_leq (y71, y72) ->
        equal_z3_expra x71 y71 && equal_z3_expra x72 y72
    | Z3BE_eq (x61, x62), Z3BE_eq (y61, y62) ->
        equal_z3_expra x61 y61 && equal_z3_expra x62 y62
    | Z3BE_or x5, Z3BE_or y5 -> Lista.equal_lista (equal_z3_bool_expr ()) x5 y5
    | Z3BE_and x4, Z3BE_and y4 ->
        Lista.equal_lista (equal_z3_bool_expr ()) x4 y4
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

module Set : sig
  type 'a set = Set of 'a list | Coset of 'a list
  val image : ('a -> 'b) -> 'a set -> 'b set
  val insert : 'a HOL.equal -> 'a -> 'a set -> 'a set
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
  val bot_set : 'a set
  val sup_set : 'a HOL.equal -> 'a set -> 'a set -> 'a set
  val less_eq_set : 'a HOL.equal -> 'a set -> 'a set -> bool
end = struct

type 'a set = Set of 'a list | Coset of 'a list;;

let rec image f (Set xs) = Set (Lista.map f xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (Lista.removeAll _A x xs)
    | x, Set xs -> Set (Lista.insert _A x xs);;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (Lista.member _A xs x)
    | x, Set xs -> Lista.member _A xs x;;

let bot_set : 'a set = Set [];;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (Lista.filter (fun x -> not (member _A x a)) xs)
    | Set xs, a -> Lista.fold (insert _A) xs a;;

let rec less_eq_set _A
  a b = match a, b with
    Coset xs, Set ys ->
      (if Lista.null xs && Lista.null ys then false
        else failwith
               "subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV"
               (fun _ -> less_eq_set _A (Coset xs) (Set ys)))
    | a, Coset ys -> Lista.list_all (fun y -> not (member _A y a)) ys
    | Set xs, b -> Lista.list_all (fun x -> member _A x b) xs;;

end;; (*struct Set*)

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
  val fmmap_keys : ('a -> 'b -> 'c) -> ('a, 'b) fmap -> ('a, 'c) fmap
  val fmlookup : 'a HOL.equal -> ('a, 'b) fmap -> 'a -> 'b option
end = struct

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (AList.merge _A m n);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec fmmap_keys
  f (Fmap_of_list m) = Fmap_of_list (Lista.map (fun (a, b) -> (a, f a b)) m);;

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
    Product_Type.equal_boola x1 y1 &&
      (Product_Type.equal_boola x2 y2 &&
        (Product_Type.equal_boola x3 y3 &&
          (Product_Type.equal_boola x4 y4 &&
            (Product_Type.equal_boola x5 y5 &&
              (Product_Type.equal_boola x6 y6 &&
                (Product_Type.equal_boola x7 y7 &&
                  Product_Type.equal_boola x8 y8))))));;

end;; (*struct Stringa*)

module SyntaxVCT : sig
  type xp = VNamed of string | VIndex
  val equal_xpa : xp -> xp -> bool
  type uop = Len | Exp | Neg | Nott | Abs
  val equal_uop : uop -> uop -> bool
  type bop = Plus | Minus | Times | Div | Mod | LEq | LT | GT | GEq | Eq | And |
    Or | NEq
  val equal_bop : bop -> bop -> bool
  type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
    L_bitvec of lit list | L_string of string | L_undef | L_real of string
  val equal_lita : lit -> lit -> bool
  val equal_lit : lit HOL.equal
  type vp = V_lit of lit | V_var of xp | V_vec of vp list | V_list of vp list |
    V_cons of vp * vp | V_constr of string * vp | V_record of (string * vp) list
    | V_tuple of vp list | V_proj of string * vp
  val equal_vpa : vp -> vp -> bool
  val equal_vp : vp HOL.equal
  type cep = CE_val of vp | CE_bop of bop * cep * cep | CE_many_plus of cep list
    | CE_uop of uop * cep | CE_proj of string * cep |
    CE_field_access of vp * string
  val equal_cepa : cep -> cep -> bool
  val equal_cep : cep HOL.equal
  type cp = C_true | C_false | C_conj of cp * cp | C_conj_many of cp list |
    C_disj of cp * cp | C_not of cp | C_eq of cep * cep | C_leq of cep * cep |
    C_imp of cp * cp
  val equal_cpa : cp -> cp -> bool
  val equal_cp : cp HOL.equal
  type order = Ord_inc | Ord_dec | Ord_def
  val equal_order : order -> order -> bool
  type bp = B_var of string | B_tid of string | B_int | B_bool | B_bit | B_unit
    | B_real | B_vec of order * bp | B_list of bp | B_tuple of bp list |
    B_union of string * (string * tau) list | B_record of (string * bp) list |
    B_undef | B_reg of tau | B_string | B_exception | B_finite_set of Z.t list
  and tau = T_refined_type of xp * bp * cp
  val equal_taua : tau -> tau -> bool
  val equal_tau : tau HOL.equal
  val equal_bpa : bp -> bp -> bool
  val equal_bp : bp HOL.equal
  type ap = A_monotype of tau | A_function of xp * bp * cp * tau
  val equal_apa : ap -> ap -> bool
  val equal_ap : ap HOL.equal
  val equal_xp : xp HOL.equal
  type bsub = BS_empty | BS_cons of bsub * bp * string
end = struct

type xp = VNamed of string | VIndex;;

let rec equal_xpa x0 x1 = match x0, x1 with VNamed x1, VIndex -> false
                    | VIndex, VNamed x1 -> false
                    | VNamed x1, VNamed y1 -> ((x1 : string) = y1)
                    | VIndex, VIndex -> true;;

type uop = Len | Exp | Neg | Nott | Abs;;

let rec equal_uop x0 x1 = match x0, x1 with Nott, Abs -> false
                    | Abs, Nott -> false
                    | Neg, Abs -> false
                    | Abs, Neg -> false
                    | Neg, Nott -> false
                    | Nott, Neg -> false
                    | Exp, Abs -> false
                    | Abs, Exp -> false
                    | Exp, Nott -> false
                    | Nott, Exp -> false
                    | Exp, Neg -> false
                    | Neg, Exp -> false
                    | Len, Abs -> false
                    | Abs, Len -> false
                    | Len, Nott -> false
                    | Nott, Len -> false
                    | Len, Neg -> false
                    | Neg, Len -> false
                    | Len, Exp -> false
                    | Exp, Len -> false
                    | Abs, Abs -> true
                    | Nott, Nott -> true
                    | Neg, Neg -> true
                    | Exp, Exp -> true
                    | Len, Len -> true;;

type bop = Plus | Minus | Times | Div | Mod | LEq | LT | GT | GEq | Eq | And |
  Or | NEq;;

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

type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
  L_bitvec of lit list | L_string of string | L_undef | L_real of string;;

let rec equal_lita
  x0 x1 = match x0, x1 with L_undef, L_real x10 -> false
    | L_real x10, L_undef -> false
    | L_string x8, L_real x10 -> false
    | L_real x10, L_string x8 -> false
    | L_string x8, L_undef -> false
    | L_undef, L_string x8 -> false
    | L_bitvec x7, L_real x10 -> false
    | L_real x10, L_bitvec x7 -> false
    | L_bitvec x7, L_undef -> false
    | L_undef, L_bitvec x7 -> false
    | L_bitvec x7, L_string x8 -> false
    | L_string x8, L_bitvec x7 -> false
    | L_num x6, L_real x10 -> false
    | L_real x10, L_num x6 -> false
    | L_num x6, L_undef -> false
    | L_undef, L_num x6 -> false
    | L_num x6, L_string x8 -> false
    | L_string x8, L_num x6 -> false
    | L_num x6, L_bitvec x7 -> false
    | L_bitvec x7, L_num x6 -> false
    | L_false, L_real x10 -> false
    | L_real x10, L_false -> false
    | L_false, L_undef -> false
    | L_undef, L_false -> false
    | L_false, L_string x8 -> false
    | L_string x8, L_false -> false
    | L_false, L_bitvec x7 -> false
    | L_bitvec x7, L_false -> false
    | L_false, L_num x6 -> false
    | L_num x6, L_false -> false
    | L_true, L_real x10 -> false
    | L_real x10, L_true -> false
    | L_true, L_undef -> false
    | L_undef, L_true -> false
    | L_true, L_string x8 -> false
    | L_string x8, L_true -> false
    | L_true, L_bitvec x7 -> false
    | L_bitvec x7, L_true -> false
    | L_true, L_num x6 -> false
    | L_num x6, L_true -> false
    | L_true, L_false -> false
    | L_false, L_true -> false
    | L_one, L_real x10 -> false
    | L_real x10, L_one -> false
    | L_one, L_undef -> false
    | L_undef, L_one -> false
    | L_one, L_string x8 -> false
    | L_string x8, L_one -> false
    | L_one, L_bitvec x7 -> false
    | L_bitvec x7, L_one -> false
    | L_one, L_num x6 -> false
    | L_num x6, L_one -> false
    | L_one, L_false -> false
    | L_false, L_one -> false
    | L_one, L_true -> false
    | L_true, L_one -> false
    | L_zero, L_real x10 -> false
    | L_real x10, L_zero -> false
    | L_zero, L_undef -> false
    | L_undef, L_zero -> false
    | L_zero, L_string x8 -> false
    | L_string x8, L_zero -> false
    | L_zero, L_bitvec x7 -> false
    | L_bitvec x7, L_zero -> false
    | L_zero, L_num x6 -> false
    | L_num x6, L_zero -> false
    | L_zero, L_false -> false
    | L_false, L_zero -> false
    | L_zero, L_true -> false
    | L_true, L_zero -> false
    | L_zero, L_one -> false
    | L_one, L_zero -> false
    | L_unit, L_real x10 -> false
    | L_real x10, L_unit -> false
    | L_unit, L_undef -> false
    | L_undef, L_unit -> false
    | L_unit, L_string x8 -> false
    | L_string x8, L_unit -> false
    | L_unit, L_bitvec x7 -> false
    | L_bitvec x7, L_unit -> false
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
    | L_real x10, L_real y10 -> ((x10 : string) = y10)
    | L_string x8, L_string y8 -> ((x8 : string) = y8)
    | L_bitvec x7, L_bitvec y7 -> Lista.equal_lista (equal_lit ()) x7 y7
    | L_num x6, L_num y6 -> Z.equal x6 y6
    | L_undef, L_undef -> true
    | L_false, L_false -> true
    | L_true, L_true -> true
    | L_one, L_one -> true
    | L_zero, L_zero -> true
    | L_unit, L_unit -> true
and equal_lit () = ({HOL.equal = equal_lita} : lit HOL.equal);;
let equal_lit = equal_lit ();;

type vp = V_lit of lit | V_var of xp | V_vec of vp list | V_list of vp list |
  V_cons of vp * vp | V_constr of string * vp | V_record of (string * vp) list |
  V_tuple of vp list | V_proj of string * vp;;

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
    | V_tuple x8, V_tuple y8 -> Lista.equal_lista (equal_vp ()) x8 y8
    | V_record x7, V_record y7 ->
        Lista.equal_lista
          (Product_Type.equal_prod Stringa.equal_literal (equal_vp ())) x7 y7
    | V_constr (x61, x62), V_constr (y61, y62) ->
        ((x61 : string) = y61) && equal_vpa x62 y62
    | V_cons (x51, x52), V_cons (y51, y52) ->
        equal_vpa x51 y51 && equal_vpa x52 y52
    | V_list x4, V_list y4 -> Lista.equal_lista (equal_vp ()) x4 y4
    | V_vec x3, V_vec y3 -> Lista.equal_lista (equal_vp ()) x3 y3
    | V_var x2, V_var y2 -> equal_xpa x2 y2
    | V_lit x1, V_lit y1 -> equal_lita x1 y1
and equal_vp () = ({HOL.equal = equal_vpa} : vp HOL.equal);;
let equal_vp = equal_vp ();;

type cep = CE_val of vp | CE_bop of bop * cep * cep | CE_many_plus of cep list |
  CE_uop of uop * cep | CE_proj of string * cep |
  CE_field_access of vp * string;;

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
        equal_vpa x61 y61 && ((x62 : string) = y62)
    | CE_proj (x51, x52), CE_proj (y51, y52) ->
        ((x51 : string) = y51) && equal_cepa x52 y52
    | CE_uop (x41, x42), CE_uop (y41, y42) ->
        equal_uop x41 y41 && equal_cepa x42 y42
    | CE_many_plus x3, CE_many_plus y3 -> Lista.equal_lista (equal_cep ()) x3 y3
    | CE_bop (x21, x22, x23), CE_bop (y21, y22, y23) ->
        equal_bop x21 y21 && (equal_cepa x22 y22 && equal_cepa x23 y23)
    | CE_val x1, CE_val y1 -> equal_vpa x1 y1
and equal_cep () = ({HOL.equal = equal_cepa} : cep HOL.equal);;
let equal_cep = equal_cep ();;

type cp = C_true | C_false | C_conj of cp * cp | C_conj_many of cp list |
  C_disj of cp * cp | C_not of cp | C_eq of cep * cep | C_leq of cep * cep |
  C_imp of cp * cp;;

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
    | C_conj_many x4, C_conj_many y4 -> Lista.equal_lista (equal_cp ()) x4 y4
    | C_conj (x31, x32), C_conj (y31, y32) ->
        equal_cpa x31 y31 && equal_cpa x32 y32
    | C_false, C_false -> true
    | C_true, C_true -> true
and equal_cp () = ({HOL.equal = equal_cpa} : cp HOL.equal);;
let equal_cp = equal_cp ();;

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

type bp = B_var of string | B_tid of string | B_int | B_bool | B_bit | B_unit |
  B_real | B_vec of order * bp | B_list of bp | B_tuple of bp list |
  B_union of string * (string * tau) list | B_record of (string * bp) list |
  B_undef | B_reg of tau | B_string | B_exception | B_finite_set of Z.t list
and tau = T_refined_type of xp * bp * cp;;

let rec equal_taua
  (T_refined_type (x1, x2, x3)) (T_refined_type (y1, y2, y3)) =
    equal_xpa x1 y1 && (equal_bpa x2 y2 && equal_cpa x3 y3)
and equal_tau () = ({HOL.equal = equal_taua} : tau HOL.equal)
and equal_bpa
  x0 x1 = match x0, x1 with B_exception, B_finite_set x17 -> false
    | B_finite_set x17, B_exception -> false
    | B_string, B_finite_set x17 -> false
    | B_finite_set x17, B_string -> false
    | B_string, B_exception -> false
    | B_exception, B_string -> false
    | B_reg x14, B_finite_set x17 -> false
    | B_finite_set x17, B_reg x14 -> false
    | B_reg x14, B_exception -> false
    | B_exception, B_reg x14 -> false
    | B_reg x14, B_string -> false
    | B_string, B_reg x14 -> false
    | B_undef, B_finite_set x17 -> false
    | B_finite_set x17, B_undef -> false
    | B_undef, B_exception -> false
    | B_exception, B_undef -> false
    | B_undef, B_string -> false
    | B_string, B_undef -> false
    | B_undef, B_reg x14 -> false
    | B_reg x14, B_undef -> false
    | B_record x12, B_finite_set x17 -> false
    | B_finite_set x17, B_record x12 -> false
    | B_record x12, B_exception -> false
    | B_exception, B_record x12 -> false
    | B_record x12, B_string -> false
    | B_string, B_record x12 -> false
    | B_record x12, B_reg x14 -> false
    | B_reg x14, B_record x12 -> false
    | B_record x12, B_undef -> false
    | B_undef, B_record x12 -> false
    | B_union (x111, x112), B_finite_set x17 -> false
    | B_finite_set x17, B_union (x111, x112) -> false
    | B_union (x111, x112), B_exception -> false
    | B_exception, B_union (x111, x112) -> false
    | B_union (x111, x112), B_string -> false
    | B_string, B_union (x111, x112) -> false
    | B_union (x111, x112), B_reg x14 -> false
    | B_reg x14, B_union (x111, x112) -> false
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
    | B_tuple x10, B_reg x14 -> false
    | B_reg x14, B_tuple x10 -> false
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
    | B_list x9, B_reg x14 -> false
    | B_reg x14, B_list x9 -> false
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
    | B_vec (x81, x82), B_reg x14 -> false
    | B_reg x14, B_vec (x81, x82) -> false
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
    | B_real, B_reg x14 -> false
    | B_reg x14, B_real -> false
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
    | B_unit, B_reg x14 -> false
    | B_reg x14, B_unit -> false
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
    | B_bit, B_reg x14 -> false
    | B_reg x14, B_bit -> false
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
    | B_bool, B_reg x14 -> false
    | B_reg x14, B_bool -> false
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
    | B_int, B_reg x14 -> false
    | B_reg x14, B_int -> false
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
    | B_tid x2, B_reg x14 -> false
    | B_reg x14, B_tid x2 -> false
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
    | B_var x1, B_reg x14 -> false
    | B_reg x14, B_var x1 -> false
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
        Lista.equal_lista Arith.equal_integer x17 y17
    | B_reg x14, B_reg y14 -> equal_taua x14 y14
    | B_record x12, B_record y12 ->
        Lista.equal_lista
          (Product_Type.equal_prod Stringa.equal_literal (equal_bp ())) x12 y12
    | B_union (x111, x112), B_union (y111, y112) ->
        ((x111 : string) = y111) &&
          Lista.equal_lista
            (Product_Type.equal_prod Stringa.equal_literal (equal_tau ())) x112
            y112
    | B_tuple x10, B_tuple y10 -> Lista.equal_lista (equal_bp ()) x10 y10
    | B_list x9, B_list y9 -> equal_bpa x9 y9
    | B_vec (x81, x82), B_vec (y81, y82) ->
        equal_order x81 y81 && equal_bpa x82 y82
    | B_tid x2, B_tid y2 -> ((x2 : string) = y2)
    | B_var x1, B_var y1 -> ((x1 : string) = y1)
    | B_exception, B_exception -> true
    | B_string, B_string -> true
    | B_undef, B_undef -> true
    | B_real, B_real -> true
    | B_unit, B_unit -> true
    | B_bit, B_bit -> true
    | B_bool, B_bool -> true
    | B_int, B_int -> true
and equal_bp () = ({HOL.equal = equal_bpa} : bp HOL.equal);;
let equal_tau = equal_tau ();;
let equal_bp = equal_bp ();;

type ap = A_monotype of tau | A_function of xp * bp * cp * tau;;

let rec equal_apa
  x0 x1 = match x0, x1 with
    A_monotype x1, A_function (x21, x22, x23, x24) -> false
    | A_function (x21, x22, x23, x24), A_monotype x1 -> false
    | A_function (x21, x22, x23, x24), A_function (y21, y22, y23, y24) ->
        equal_xpa x21 y21 &&
          (equal_bpa x22 y22 && (equal_cpa x23 y23 && equal_taua x24 y24))
    | A_monotype x1, A_monotype y1 -> equal_taua x1 y1;;

let equal_ap = ({HOL.equal = equal_apa} : ap HOL.equal);;

let equal_xp = ({HOL.equal = equal_xpa} : xp HOL.equal);;

type bsub = BS_empty | BS_cons of bsub * bp * string;;

end;; (*struct SyntaxVCT*)

module Location : sig
  type 'a pos_ext = Pos_ext of string * Z.t * Z.t * Z.t * 'a
  type loc = Loc_unknown | Loc_range of unit pos_ext * unit pos_ext
  val equal_pos_ext : 'a HOL.equal -> 'a pos_ext -> 'a pos_ext -> bool
  val equal_loc : loc -> loc -> bool
end = struct

type 'a pos_ext = Pos_ext of string * Z.t * Z.t * Z.t * 'a;;

type loc = Loc_unknown | Loc_range of unit pos_ext * unit pos_ext;;

let rec equal_pos_ext _A
  (Pos_ext (pos_fnamea, pos_lnuma, pos_bola, pos_cnuma, morea))
    (Pos_ext (pos_fname, pos_lnum, pos_bol, pos_cnum, more)) =
    ((pos_fnamea : string) = pos_fname) &&
      (Z.equal pos_lnuma pos_lnum &&
        (Z.equal pos_bola pos_bol &&
          (Z.equal pos_cnuma pos_cnum && HOL.eq _A morea more)));;

let rec equal_loc
  x0 x1 = match x0, x1 with Loc_unknown, Loc_range (x21, x22) -> false
    | Loc_range (x21, x22), Loc_unknown -> false
    | Loc_range (x21, x22), Loc_range (y21, y22) ->
        equal_pos_ext Product_Type.equal_unit x21 y21 &&
          equal_pos_ext Product_Type.equal_unit x22 y22
    | Loc_unknown, Loc_unknown -> true;;

end;; (*struct Location*)

module SyntaxPED : sig
  type patp = Pp_lit of Location.loc * SyntaxVCT.lit | Pp_wild of Location.loc |
    Pp_as_var of Location.loc * patp * SyntaxVCT.xp |
    Pp_typ of Location.loc * SyntaxVCT.tau * patp |
    Pp_id of Location.loc * string |
    Pp_as_typ of Location.loc * patp * SyntaxVCT.tau |
    Pp_app of Location.loc * string * patp list |
    Pp_vector of Location.loc * patp list |
    Pp_vector_concat of Location.loc * patp list |
    Pp_tup of Location.loc * patp list | Pp_list of Location.loc * patp list |
    Pp_cons of Location.loc * patp * patp |
    Pp_string_append of Location.loc * patp list
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
    Ep_assign of Location.loc * lexpp * ep * ep | Ep_return of Location.loc * ep
    | Ep_exit of Location.loc * ep | Ep_ref of Location.loc * string |
    Ep_throw of Location.loc * ep | Ep_try of Location.loc * ep * pexpp list |
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
  val fvs_bp : SyntaxVCT.bp -> SyntaxVCT.xp list
  val fvs_tau : SyntaxVCT.tau -> SyntaxVCT.xp list
  val fvs_ctor_tau : string * SyntaxVCT.tau -> SyntaxVCT.xp list
  val fvs_ctor_tau_list : (string * SyntaxVCT.tau) list -> SyntaxVCT.xp list
  val fvs_bp_list : SyntaxVCT.bp list -> SyntaxVCT.xp list
  val fvs_field_bp : string * SyntaxVCT.bp -> SyntaxVCT.xp list
  val fvs_field_bp_list : (string * SyntaxVCT.bp) list -> SyntaxVCT.xp list
  val fvs_patp : patp -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_app : patp list -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_tup : patp list -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_list : patp list -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_vector : patp list -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_string_append : patp list -> SyntaxVCT.xp list
  val fvs_patp_list_Pp_vector_concat : patp list -> SyntaxVCT.xp list
  val list_minus : 'a HOL.equal -> 'a list -> 'a list -> 'a list
  val fvs_lexpp : lexpp -> SyntaxVCT.xp list
  val fvs_lexpp_list : lexpp list -> SyntaxVCT.xp list
  val fvs_ep : ep -> SyntaxVCT.xp list
  val fvs_pexpp : pexpp -> SyntaxVCT.xp list
  val fvs_pexpp_list_Ep_try : pexpp list -> SyntaxVCT.xp list
  val fvs_pexpp_list_Ep_case : pexpp list -> SyntaxVCT.xp list
  val fvs_letbind : letbind -> SyntaxVCT.xp list
  val fvs_ep_list_Ep_vec : ep list -> SyntaxVCT.xp list
  val fvs_ep_list_Ep_list : ep list -> SyntaxVCT.xp list
  val fvs_ep_list_Ep_block : ep list -> SyntaxVCT.xp list
  val fvs_ep_list_Ep_tuple : ep list -> SyntaxVCT.xp list
  val fvs_ep_list_Ep_concat : ep list -> SyntaxVCT.xp list
  val fvs_field_ep_Ep_record : string * ep -> SyntaxVCT.xp list
  val fvs_field_ep_list_Ep_record : (string * ep) list -> SyntaxVCT.xp list
  val fvs_field_ep_Ep_record_update : string * ep -> SyntaxVCT.xp list
  val fvs_field_ep_list_Ep_record_update :
    (string * ep) list -> SyntaxVCT.xp list
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
  val tsubst_bsub : SyntaxVCT.bp -> string -> SyntaxVCT.bsub -> SyntaxVCT.bsub
  val ce_subst_funclp : SyntaxVCT.cep -> SyntaxVCT.xp -> funclp -> funclp
end = struct

type patp = Pp_lit of Location.loc * SyntaxVCT.lit | Pp_wild of Location.loc |
  Pp_as_var of Location.loc * patp * SyntaxVCT.xp |
  Pp_typ of Location.loc * SyntaxVCT.tau * patp | Pp_id of Location.loc * string
  | Pp_as_typ of Location.loc * patp * SyntaxVCT.tau |
  Pp_app of Location.loc * string * patp list |
  Pp_vector of Location.loc * patp list |
  Pp_vector_concat of Location.loc * patp list |
  Pp_tup of Location.loc * patp list | Pp_list of Location.loc * patp list |
  Pp_cons of Location.loc * patp * patp |
  Pp_string_append of Location.loc * patp list;;

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
  Ep_assign of Location.loc * lexpp * ep * ep | Ep_return of Location.loc * ep |
  Ep_exit of Location.loc * ep | Ep_ref of Location.loc * string |
  Ep_throw of Location.loc * ep | Ep_try of Location.loc * ep * pexpp list |
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

let rec fvs_bp
  = function SyntaxVCT.B_var tvar -> []
    | SyntaxVCT.B_tid id -> []
    | SyntaxVCT.B_int -> []
    | SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_real -> []
    | SyntaxVCT.B_vec (order, bp) -> fvs_bp bp
    | SyntaxVCT.B_list bp -> fvs_bp bp
    | SyntaxVCT.B_tuple bp_list -> fvs_bp_list bp_list
    | SyntaxVCT.B_union (id, ctor_tau_list) -> fvs_ctor_tau_list ctor_tau_list
    | SyntaxVCT.B_record field_bp_list -> fvs_field_bp_list field_bp_list
    | SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_reg tau -> fvs_tau tau
    | SyntaxVCT.B_string -> []
    | SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_finite_set num_list -> []
and fvs_tau (SyntaxVCT.T_refined_type (zp, bp, cp)) = fvs_bp bp @ fvs_cp cp
and fvs_ctor_tau (ctor_XXX, tau_XXX) = fvs_tau tau_XXX
and fvs_ctor_tau_list
  = function [] -> []
    | ctor_tau_XXX :: ctor_tau_list_XXX ->
        fvs_ctor_tau ctor_tau_XXX @ fvs_ctor_tau_list ctor_tau_list_XXX
and fvs_bp_list
  = function [] -> []
    | bp_XXX :: bp_list_XXX -> fvs_bp bp_XXX @ fvs_bp_list bp_list_XXX
and fvs_field_bp (field_XXX, bp_XXX) = fvs_bp bp_XXX
and fvs_field_bp_list
  = function [] -> []
    | field_bp_XXX :: field_bp_list_XXX ->
        fvs_field_bp field_bp_XXX @ fvs_field_bp_list field_bp_list_XXX;;

let rec fvs_patp
  = function Pp_lit (loc, lit) -> []
    | Pp_wild loc -> []
    | Pp_as_var (loc, patp, xp) -> fvs_patp patp
    | Pp_typ (loc, tau, patp) -> fvs_tau tau @ fvs_patp patp
    | Pp_id (loc, id) -> []
    | Pp_as_typ (loc, patp, tau) -> fvs_patp patp @ fvs_tau tau
    | Pp_app (loc, id, patp_list) -> fvs_patp_list_Pp_app patp_list
    | Pp_vector (loc, patp_list) -> fvs_patp_list_Pp_vector patp_list
    | Pp_vector_concat (loc, patp_list) ->
        fvs_patp_list_Pp_vector_concat patp_list
    | Pp_tup (loc, patp_list) -> fvs_patp_list_Pp_tup patp_list
    | Pp_list (loc, patp_list) -> fvs_patp_list_Pp_list patp_list
    | Pp_cons (loc, patp1, patp2) -> fvs_patp patp1 @ fvs_patp patp2
    | Pp_string_append (loc, patp_list) ->
        fvs_patp_list_Pp_string_append patp_list
and fvs_patp_list_Pp_app
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_app patp_list_XXX
and fvs_patp_list_Pp_tup
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_tup patp_list_XXX
and fvs_patp_list_Pp_list
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_list patp_list_XXX
and fvs_patp_list_Pp_vector
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_vector patp_list_XXX
and fvs_patp_list_Pp_string_append
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_string_append patp_list_XXX
and fvs_patp_list_Pp_vector_concat
  = function [] -> []
    | patp_XXX :: patp_list_XXX ->
        fvs_patp patp_XXX @ fvs_patp_list_Pp_vector_concat patp_list_XXX;;

let rec list_minus _A
  x0 ys = match x0, ys with [], ys -> []
    | x :: xs, ys ->
        (if not (Lista.member _A ys x) then x :: list_minus _A xs ys
          else list_minus _A xs ys);;

let rec fvs_lexpp = function LEXPp_mvar (loc, up) -> []
                    | LEXPp_cast (loc, tau, up) -> fvs_tau tau
                    | LEXPp_tup (loc, lexpp_list) -> fvs_lexpp_list lexpp_list
                    | LEXPp_field (loc, lexpp, id) -> fvs_lexpp lexpp
and fvs_lexpp_list
  = function [] -> []
    | lexpp_XXX :: lexpp_list_XXX ->
        fvs_lexpp lexpp_XXX @ fvs_lexpp_list lexpp_list_XXX;;

let rec fvs_ep
  = function Ep_val (loc, vp) -> fvs_vp vp
    | Ep_mvar (loc, up) -> []
    | Ep_concat (loc, ep_list) -> fvs_ep_list_Ep_concat ep_list
    | Ep_tuple (loc, ep_list) -> fvs_ep_list_Ep_tuple ep_list
    | Ep_app (loc, fp, ep) -> fvs_ep ep
    | Ep_bop (loc, bop, ep1, ep2) -> fvs_ep ep1 @ fvs_ep ep2
    | Ep_uop (loc, uop, ep) -> fvs_ep ep
    | Ep_proj (loc, p, ep) -> fvs_ep ep
    | Ep_constr (loc, ctor, ep) -> fvs_ep ep
    | Ep_field_access (loc, ep, field) -> fvs_ep ep
    | Ep_sizeof (loc, cep) -> fvs_cep cep
    | Ep_cast (loc, tau, ep) -> fvs_tau tau @ fvs_ep ep
    | Ep_record (loc, field_ep_list) ->
        fvs_field_ep_list_Ep_record field_ep_list
    | Ep_record_update (loc, ep, field_ep_list) ->
        fvs_ep ep @ fvs_field_ep_list_Ep_record_update field_ep_list
    | Ep_let (loc, letbind, ep2) -> fvs_letbind letbind @ fvs_ep ep2
    | Ep_let2 (loc, xp, tau, ep1, ep2) ->
        fvs_tau tau @
          fvs_ep ep1 @ list_minus SyntaxVCT.equal_xp (fvs_ep ep2) [xp]
    | Ep_if (loc, ep1, ep2, ep3) -> fvs_ep ep1 @ fvs_ep ep2 @ fvs_ep ep3
    | Ep_block (loc, ep_list) -> fvs_ep_list_Ep_block ep_list
    | Ep_case (loc, ep, pexpp_list) ->
        fvs_ep ep @ fvs_pexpp_list_Ep_case pexpp_list
    | Ep_assign (loc, lexpp, ep1, ep2) ->
        fvs_lexpp lexpp @ fvs_ep ep1 @ fvs_ep ep2
    | Ep_return (loc, ep) -> fvs_ep ep
    | Ep_exit (loc, ep) -> fvs_ep ep
    | Ep_ref (loc, id) -> []
    | Ep_throw (loc, ep) -> fvs_ep ep
    | Ep_try (loc, ep, pexpp_list) ->
        fvs_ep ep @ fvs_pexpp_list_Ep_try pexpp_list
    | Ep_constraint (loc, cp) -> fvs_cp cp
    | Ep_loop (loc, loop, ep1, ep2) -> fvs_ep ep1 @ fvs_ep ep2
    | Ep_for (loc, id, ep1, ep2, ep3, order, ep4) ->
        fvs_ep ep1 @ fvs_ep ep2 @ fvs_ep ep3 @ fvs_ep ep4
    | Ep_assert (loc, ep1, ep2) -> fvs_ep ep1 @ fvs_ep ep2
    | Ep_vec (loc, ep_list) -> fvs_ep_list_Ep_vec ep_list
    | Ep_list (loc, ep_list) -> fvs_ep_list_Ep_list ep_list
    | Ep_cons (loc, ep1, ep2) -> fvs_ep ep1 @ fvs_ep ep2
and fvs_pexpp
  = function PEXPp_exp (patp, ep) -> fvs_patp patp @ fvs_ep ep
    | PEXPp_when (patp, ep1, ep2) -> fvs_patp patp @ fvs_ep ep1 @ fvs_ep ep2
and fvs_pexpp_list_Ep_try
  = function [] -> []
    | pexpp_XXX :: pexpp_list_XXX ->
        fvs_pexpp pexpp_XXX @ fvs_pexpp_list_Ep_try pexpp_list_XXX
and fvs_pexpp_list_Ep_case
  = function [] -> []
    | pexpp_XXX :: pexpp_list_XXX ->
        fvs_pexpp pexpp_XXX @ fvs_pexpp_list_Ep_case pexpp_list_XXX
and fvs_letbind (LBp_val (loc, patp, ep)) = fvs_patp patp @ fvs_ep ep
and fvs_ep_list_Ep_vec
  = function [] -> []
    | ep_XXX :: ep_list_XXX -> fvs_ep ep_XXX @ fvs_ep_list_Ep_vec ep_list_XXX
and fvs_ep_list_Ep_list
  = function [] -> []
    | ep_XXX :: ep_list_XXX -> fvs_ep ep_XXX @ fvs_ep_list_Ep_list ep_list_XXX
and fvs_ep_list_Ep_block
  = function [] -> []
    | ep_XXX :: ep_list_XXX -> fvs_ep ep_XXX @ fvs_ep_list_Ep_block ep_list_XXX
and fvs_ep_list_Ep_tuple
  = function [] -> []
    | ep_XXX :: ep_list_XXX -> fvs_ep ep_XXX @ fvs_ep_list_Ep_tuple ep_list_XXX
and fvs_ep_list_Ep_concat
  = function [] -> []
    | ep_XXX :: ep_list_XXX -> fvs_ep ep_XXX @ fvs_ep_list_Ep_concat ep_list_XXX
and fvs_field_ep_Ep_record (field_XXX, ep_XXX) = fvs_ep ep_XXX
and fvs_field_ep_list_Ep_record
  = function [] -> []
    | field_ep_XXX :: field_ep_list_XXX ->
        fvs_field_ep_Ep_record field_ep_XXX @
          fvs_field_ep_list_Ep_record field_ep_list_XXX
and fvs_field_ep_Ep_record_update (field_XXX, ep_XXX) = fvs_ep ep_XXX
and fvs_field_ep_list_Ep_record_update
  = function [] -> []
    | field_ep_XXX :: field_ep_list_XXX ->
        fvs_field_ep_Ep_record_update field_ep_XXX @
          fvs_field_ep_list_Ep_record_update field_ep_list_XXX;;

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
                | Ep_return (x211, x212) -> x211
                | Ep_exit (x221, x222) -> x221
                | Ep_ref (x231, x232) -> x231
                | Ep_throw (x241, x242) -> x241
                | Ep_try (x251, x252, x253) -> x251
                | Ep_constraint (x261, x262) -> x261
                | Ep_loop (x271, x272, x273, x274) -> x271
                | Ep_for (x281, x282, x283, x284, x285, x286, x287) -> x281
                | Ep_assert (x291, x292, x293) -> x291
                | Ep_vec (x301, x302) -> x301
                | Ep_list (x311, x312) -> x311
                | Ep_cons (x321, x322, x323) -> x321;;

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
    | vp5, zp5, SyntaxVCT.B_reg tau -> SyntaxVCT.B_reg (subst_tp vp5 zp5 tau)
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
    vp5, zp5, Pp_lit (loc, lit) -> Pp_lit (loc, lit)
    | vp5, zp5, Pp_wild loc -> Pp_wild loc
    | vp5, zp5, Pp_as_var (loc, patp, xp) ->
        Pp_as_var (loc, subst_patp vp5 zp5 patp, xp)
    | vp5, zp5, Pp_typ (loc, tau, patp) ->
        Pp_typ (loc, subst_tp vp5 zp5 tau, subst_patp vp5 zp5 patp)
    | vp5, zp5, Pp_id (loc, id) -> Pp_id (loc, id)
    | vp5, zp5, Pp_as_typ (loc, patp, tau) ->
        Pp_as_typ (loc, subst_patp vp5 zp5 patp, subst_tp vp5 zp5 tau)
    | vp5, zp5, Pp_app (loc, id, patp_list) ->
        Pp_app (loc, id, subst_patp_list_Pp_app vp5 zp5 patp_list)
    | vp5, zp5, Pp_vector (loc, patp_list) ->
        Pp_vector (loc, subst_patp_list_Pp_vector vp5 zp5 patp_list)
    | vp5, zp5, Pp_vector_concat (loc, patp_list) ->
        Pp_vector_concat
          (loc, subst_patp_list_Pp_vector_concat vp5 zp5 patp_list)
    | vp5, zp5, Pp_tup (loc, patp_list) ->
        Pp_tup (loc, subst_patp_list_Pp_tup vp5 zp5 patp_list)
    | vp5, zp5, Pp_list (loc, patp_list) ->
        Pp_list (loc, subst_patp_list_Pp_list vp5 zp5 patp_list)
    | vp5, zp5, Pp_cons (loc, patp1, patp2) ->
        Pp_cons (loc, subst_patp vp5 zp5 patp1, subst_patp vp5 zp5 patp2)
    | vp5, zp5, Pp_string_append (loc, patp_list) ->
        Pp_string_append
          (loc, subst_patp_list_Pp_string_append vp5 zp5 patp_list)
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
    | vp5, zp5, Ep_return (loc, ep) -> Ep_return (loc, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_exit (loc, ep) -> Ep_exit (loc, subst_ep vp5 zp5 ep)
    | vp5, zp5, Ep_ref (loc, id) -> Ep_ref (loc, id)
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
    | bp_5, tvar5, SyntaxVCT.B_reg tau ->
        SyntaxVCT.B_reg (tsubst_tp bp_5 tvar5 tau)
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
    cep_5, zp5, SyntaxVCT.CE_val v ->
      (match v with SyntaxVCT.V_lit _ -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_var x ->
          (if SyntaxVCT.equal_xpa x zp5 then cep_5 else SyntaxVCT.CE_val v)
        | SyntaxVCT.V_vec _ -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_list _ -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_cons (_, _) -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_constr (_, _) -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_record _ -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_tuple _ -> SyntaxVCT.CE_val v
        | SyntaxVCT.V_proj (_, _) -> SyntaxVCT.CE_val v)
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
    | cep5, zp5, SyntaxVCT.B_reg tau ->
        SyntaxVCT.B_reg (ce_subst_tp cep5 zp5 tau)
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
    cep5, zp5, Pp_lit (loc, lit) -> Pp_lit (loc, lit)
    | cep5, zp5, Pp_wild loc -> Pp_wild loc
    | cep5, zp5, Pp_as_var (loc, patp, xp) ->
        Pp_as_var (loc, ce_subst_patp cep5 zp5 patp, xp)
    | cep5, zp5, Pp_typ (loc, tau, patp) ->
        Pp_typ (loc, ce_subst_tp cep5 zp5 tau, ce_subst_patp cep5 zp5 patp)
    | cep5, zp5, Pp_id (loc, id) -> Pp_id (loc, id)
    | cep5, zp5, Pp_as_typ (loc, patp, tau) ->
        Pp_as_typ (loc, ce_subst_patp cep5 zp5 patp, ce_subst_tp cep5 zp5 tau)
    | cep5, zp5, Pp_app (loc, id, patp_list) ->
        Pp_app (loc, id, ce_subst_patp_list_Pp_app cep5 zp5 patp_list)
    | cep5, zp5, Pp_vector (loc, patp_list) ->
        Pp_vector (loc, ce_subst_patp_list_Pp_vector cep5 zp5 patp_list)
    | cep5, zp5, Pp_vector_concat (loc, patp_list) ->
        Pp_vector_concat
          (loc, ce_subst_patp_list_Pp_vector_concat cep5 zp5 patp_list)
    | cep5, zp5, Pp_tup (loc, patp_list) ->
        Pp_tup (loc, ce_subst_patp_list_Pp_tup cep5 zp5 patp_list)
    | cep5, zp5, Pp_list (loc, patp_list) ->
        Pp_list (loc, ce_subst_patp_list_Pp_list cep5 zp5 patp_list)
    | cep5, zp5, Pp_cons (loc, patp1, patp2) ->
        Pp_cons
          (loc, ce_subst_patp cep5 zp5 patp1, ce_subst_patp cep5 zp5 patp2)
    | cep5, zp5, Pp_string_append (loc, patp_list) ->
        Pp_string_append
          (loc, ce_subst_patp_list_Pp_string_append cep5 zp5 patp_list)
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
    | cep5, zp5, Ep_return (loc, ep) -> Ep_return (loc, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_exit (loc, ep) -> Ep_exit (loc, ce_subst_ep cep5 zp5 ep)
    | cep5, zp5, Ep_ref (loc, id) -> Ep_ref (loc, id)
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

let rec tsubst_bsub
  bp5 tvar5 x2 = match bp5, tvar5, x2 with
    bp5, tvar5, SyntaxVCT.BS_empty -> SyntaxVCT.BS_empty
    | bp5, tvar5, SyntaxVCT.BS_cons (bsub, bp, tvar) ->
        SyntaxVCT.BS_cons
          (tsubst_bsub bp5 tvar5 bsub, tsubst_bp bp5 tvar5 bp, tvar);;

let rec ce_subst_funclp
  cep5 zp5 (FCLp_funcl (loc, id, pexpp)) =
    FCLp_funcl (loc, id, ce_subst_pexpp cep5 zp5 pexpp);;

end;; (*struct SyntaxPED*)

module Utils : sig
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val string_of_digit : Arith.nat -> Stringa.char list
  val string_of_nat : Arith.nat -> Stringa.char list
  val string_of_int : Arith.int -> Stringa.char list
  val string_lit_map : string -> ('a -> string) -> 'a list -> string
  val string_lit_concat : string list -> string
  val string_lit_of_int : Arith.int -> string
  val string_lit_of_nat : Arith.nat -> string
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

let rec string_lit_concat s = Lista.foldr (fun a b -> a ^ b) s "";;

let rec string_lit_of_int x = Fun.comp Stringa.implode string_of_int x;;

let rec string_lit_of_nat x = Fun.comp Stringa.implode string_of_nat x;;

let rec string_lit_of_integer
  x = Fun.comp string_lit_of_int (fun a -> Arith.Int_of_integer a) x;;

end;; (*struct Utils*)

module SyntaxUtils : sig
  val mk_proj_eq_x : SyntaxVCT.xp -> SyntaxVCT.xp -> string -> SyntaxVCT.cp
  val b_of : SyntaxVCT.tau -> SyntaxVCT.bp
  val aux :
    SyntaxVCT.xp ->
      string -> SyntaxVCT.tau -> (string * SyntaxVCT.bp) * SyntaxVCT.cp
  val c_of : SyntaxVCT.tau -> SyntaxVCT.cp
  val rv_id : string -> (string, string) Finite_Map.fmap -> string
  val rv_xp : SyntaxVCT.xp -> (string, string) Finite_Map.fmap -> SyntaxVCT.xp
  val rv_vp : SyntaxVCT.vp -> (string, string) Finite_Map.fmap -> SyntaxVCT.vp
  val rv_cep :
    SyntaxVCT.cep -> (string, string) Finite_Map.fmap -> SyntaxVCT.cep
  val rv_cp : SyntaxVCT.cp -> (string, string) Finite_Map.fmap -> SyntaxVCT.cp
  val rv_t : SyntaxVCT.tau -> (string, string) Finite_Map.fmap -> SyntaxVCT.tau
  val rv_pat :
    SyntaxPED.patp -> (string, string) Finite_Map.fmap -> SyntaxPED.patp
  val rv_lexpp :
    SyntaxPED.lexpp -> (string, string) Finite_Map.fmap -> SyntaxPED.lexpp
  val rv_ep : SyntaxPED.ep -> (string, string) Finite_Map.fmap -> SyntaxPED.ep
  val rv_pexpp :
    SyntaxPED.pexpp -> (string, string) Finite_Map.fmap -> SyntaxPED.pexpp
  val rv_letbind :
    SyntaxPED.letbind -> (string, string) Finite_Map.fmap -> SyntaxPED.letbind
  val mk_new : 'a list -> string -> string
  val pat_id : SyntaxPED.patp -> string list
  val unzip3 : ('a * ('b * 'c)) list -> 'a list * ('b list * 'c list)
  val b_of_lit : SyntaxVCT.lit -> SyntaxVCT.bp
  val mk_fresh_aux : string list -> string list -> string -> string
  val mk_fresh : string list -> string -> string
  val mk_l_eq_c : SyntaxVCT.xp -> SyntaxVCT.lit -> SyntaxVCT.cp
  val mk_l_eq_t : SyntaxVCT.lit -> SyntaxVCT.tau
  val mk_list_c : SyntaxVCT.xp -> SyntaxVCT.xp list -> SyntaxVCT.cp
  val mk_v_eq_c : SyntaxVCT.xp -> SyntaxVCT.vp -> SyntaxVCT.cp
  val mk_v_eq_t : SyntaxVCT.bp -> SyntaxVCT.vp -> SyntaxVCT.tau
  val mk_mapping :
    string list -> string list -> (string, string) Finite_Map.fmap
  val freshen_pexp_aux :
    string list ->
      SyntaxPED.patp -> SyntaxPED.ep -> SyntaxPED.patp * SyntaxPED.ep
  val freshen_ep : string list -> SyntaxPED.ep -> SyntaxPED.ep
  val freshen_pexpp : string list -> SyntaxPED.pexpp -> SyntaxPED.pexpp
  val mk_eq_proj :
    Location.loc -> SyntaxVCT.xp -> Arith.nat -> Arith.nat -> SyntaxVCT.cp
  val mk_proj_eq : SyntaxVCT.xp -> string -> SyntaxVCT.cp
  val c_conj_list : SyntaxVCT.cp list -> SyntaxVCT.cp
  val mk_record_b_c :
    SyntaxVCT.xp list ->
      (string * SyntaxVCT.tau) list -> SyntaxVCT.bp * SyntaxVCT.cp
  val mk_vec_len_eq_c : SyntaxVCT.xp -> 'a list -> SyntaxVCT.cp
  val mk_x_eq_c_tuple : SyntaxVCT.xp -> SyntaxVCT.xp list -> SyntaxVCT.cp
  val subst_x_cp : SyntaxVCT.cp -> SyntaxVCT.xp -> SyntaxVCT.vp -> SyntaxVCT.cp
end = struct

let rec mk_proj_eq_x
  x y field =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var y),
        SyntaxVCT.CE_val (SyntaxVCT.V_proj (field, SyntaxVCT.V_var x)));;

let rec b_of (SyntaxVCT.T_refined_type (uu, b, uv)) = b;;

let rec aux z f t = ((f, b_of t), mk_proj_eq_x SyntaxVCT.VIndex z f);;

let rec c_of (SyntaxVCT.T_refined_type (uu, uv, c)) = c;;

let rec rv_id
  xp fm =
    (match Finite_Map.fmlookup Stringa.equal_literal fm xp with None -> xp
      | Some xpa -> xpa);;

let rec rv_xp
  x0 fm = match x0, fm with
    SyntaxVCT.VNamed xp, fm -> SyntaxVCT.VNamed (rv_id xp fm)
    | SyntaxVCT.VIndex, uu -> SyntaxVCT.VIndex;;

let rec rv_vp
  x0 fm = match x0, fm with
    SyntaxVCT.V_var xp, fm -> SyntaxVCT.V_var (rv_xp xp fm)
    | SyntaxVCT.V_lit lit, fm -> SyntaxVCT.V_lit lit
    | SyntaxVCT.V_vec vp_list, fm ->
        SyntaxVCT.V_vec (Lista.map (fun p -> rv_vp p fm) vp_list)
    | SyntaxVCT.V_list vp_list, fm ->
        SyntaxVCT.V_list (Lista.map (fun p -> rv_vp p fm) vp_list)
    | SyntaxVCT.V_cons (vp1, vp2), fm ->
        SyntaxVCT.V_cons (rv_vp vp1 fm, rv_vp vp2 fm)
    | SyntaxVCT.V_constr (ctor, vp), fm ->
        SyntaxVCT.V_constr (ctor, rv_vp vp fm)
    | SyntaxVCT.V_record fs, fm ->
        SyntaxVCT.V_record (Lista.map (fun (f, p) -> (f, rv_vp p fm)) fs)
    | SyntaxVCT.V_tuple vp_list, fm ->
        SyntaxVCT.V_tuple (Lista.map (fun p -> rv_vp p fm) vp_list)
    | SyntaxVCT.V_proj (s, vp), fm -> SyntaxVCT.V_proj (s, rv_vp vp fm);;

let rec rv_cep
  x0 fm = match x0, fm with
    SyntaxVCT.CE_val vp, fm -> SyntaxVCT.CE_val (rv_vp vp fm)
    | SyntaxVCT.CE_bop (bop, cep1, cep2), fm ->
        SyntaxVCT.CE_bop (bop, rv_cep cep1 fm, rv_cep cep2 fm)
    | SyntaxVCT.CE_many_plus cep_list, fm ->
        SyntaxVCT.CE_many_plus (Lista.map (fun c -> rv_cep c fm) cep_list)
    | SyntaxVCT.CE_uop (uop, cep), fm -> SyntaxVCT.CE_uop (uop, rv_cep cep fm)
    | SyntaxVCT.CE_proj (p, cep), fm -> SyntaxVCT.CE_proj (p, rv_cep cep fm)
    | SyntaxVCT.CE_field_access (vp, field), fm ->
        SyntaxVCT.CE_field_access (rv_vp vp fm, field);;

let rec rv_cp
  x0 fm = match x0, fm with SyntaxVCT.C_true, fm -> SyntaxVCT.C_true
    | SyntaxVCT.C_false, fm -> SyntaxVCT.C_false
    | SyntaxVCT.C_conj (cp1, cp2), fm ->
        SyntaxVCT.C_conj (rv_cp cp1 fm, rv_cp cp2 fm)
    | SyntaxVCT.C_conj_many cp_list, fm ->
        SyntaxVCT.C_conj_many (Lista.map (fun c -> rv_cp c fm) cp_list)
    | SyntaxVCT.C_disj (cp1, cp2), fm ->
        SyntaxVCT.C_disj (rv_cp cp1 fm, rv_cp cp2 fm)
    | SyntaxVCT.C_not cp, fm -> SyntaxVCT.C_not (rv_cp cp fm)
    | SyntaxVCT.C_eq (cep1, cep2), fm ->
        SyntaxVCT.C_eq (rv_cep cep1 fm, rv_cep cep2 fm)
    | SyntaxVCT.C_leq (cep1, cep2), fm ->
        SyntaxVCT.C_leq (rv_cep cep1 fm, rv_cep cep2 fm)
    | SyntaxVCT.C_imp (cp1, cp2), fm ->
        SyntaxVCT.C_imp (rv_cp cp1 fm, rv_cp cp2 fm);;

let rec rv_t
  (SyntaxVCT.T_refined_type (SyntaxVCT.VIndex, b, cp)) fm =
    SyntaxVCT.T_refined_type (SyntaxVCT.VIndex, b, rv_cp cp fm);;

let rec rv_pat
  x0 fm = match x0, fm with
    SyntaxPED.Pp_id (loc, xp), fm ->
      (match Finite_Map.fmlookup Stringa.equal_literal fm xp
        with None -> SyntaxPED.Pp_id (loc, xp)
        | Some a -> SyntaxPED.Pp_id (loc, a))
    | SyntaxPED.Pp_wild l, fm -> SyntaxPED.Pp_wild l
    | SyntaxPED.Pp_lit (loc, l), fm -> SyntaxPED.Pp_lit (loc, l)
    | SyntaxPED.Pp_as_var (loc, patp, xp), fm ->
        SyntaxPED.Pp_as_var (loc, rv_pat patp fm, rv_xp xp fm)
    | SyntaxPED.Pp_typ (loc, tau, patp), fm ->
        SyntaxPED.Pp_typ (loc, rv_t tau fm, rv_pat patp fm)
    | SyntaxPED.Pp_as_typ (loc, patp, tau), fm ->
        SyntaxPED.Pp_as_typ (loc, rv_pat patp fm, rv_t tau fm)
    | SyntaxPED.Pp_app (loc, idd, patp_list), fm ->
        SyntaxPED.Pp_app (loc, idd, Lista.map (fun p -> rv_pat p fm) patp_list)
    | SyntaxPED.Pp_vector (loc, patp_list), fm ->
        SyntaxPED.Pp_vector (loc, Lista.map (fun p -> rv_pat p fm) patp_list)
    | SyntaxPED.Pp_vector_concat (loc, patp_list), fm ->
        SyntaxPED.Pp_vector_concat
          (loc, Lista.map (fun p -> rv_pat p fm) patp_list)
    | SyntaxPED.Pp_tup (loc, patp_list), fm ->
        SyntaxPED.Pp_tup (loc, Lista.map (fun p -> rv_pat p fm) patp_list)
    | SyntaxPED.Pp_list (loc, patp_list), fm ->
        SyntaxPED.Pp_list (loc, Lista.map (fun p -> rv_pat p fm) patp_list)
    | SyntaxPED.Pp_cons (loc, patp1, patp2), fm ->
        SyntaxPED.Pp_cons (loc, rv_pat patp1 fm, rv_pat patp2 fm)
    | SyntaxPED.Pp_string_append (loc, patp_list), fm ->
        SyntaxPED.Pp_string_append
          (loc, Lista.map (fun p -> rv_pat p fm) patp_list);;

let rec rv_lexpp
  x0 fm = match x0, fm with
    SyntaxPED.LEXPp_mvar (loc, up), fm -> SyntaxPED.LEXPp_mvar (loc, up)
    | SyntaxPED.LEXPp_cast (loc, tau, up), fm ->
        SyntaxPED.LEXPp_cast (loc, rv_t tau fm, up)
    | SyntaxPED.LEXPp_tup (loc, lexpp_list), fm ->
        SyntaxPED.LEXPp_tup (loc, Lista.map (fun l -> rv_lexpp l fm) lexpp_list)
    | SyntaxPED.LEXPp_field (loc, lexpp, idd), fm ->
        SyntaxPED.LEXPp_field (loc, rv_lexpp lexpp fm, idd);;

let rec rv_ep
  x0 fm = match x0, fm with
    SyntaxPED.Ep_val (loc, v), fm -> SyntaxPED.Ep_val (loc, rv_vp v fm)
    | SyntaxPED.Ep_mvar (loc, up), fm -> SyntaxPED.Ep_mvar (loc, up)
    | SyntaxPED.Ep_concat (loc, ep_list), fm ->
        SyntaxPED.Ep_concat (loc, Lista.map (fun e -> rv_ep e fm) ep_list)
    | SyntaxPED.Ep_tuple (loc, ep_list), fm ->
        SyntaxPED.Ep_tuple (loc, Lista.map (fun e -> rv_ep e fm) ep_list)
    | SyntaxPED.Ep_app (loc, fp, ep), fm ->
        SyntaxPED.Ep_app (loc, fp, rv_ep ep fm)
    | SyntaxPED.Ep_bop (loc, bop, ep1, ep2), fm ->
        SyntaxPED.Ep_bop (loc, bop, rv_ep ep1 fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_uop (loc, uop, ep), fm ->
        SyntaxPED.Ep_uop (loc, uop, rv_ep ep fm)
    | SyntaxPED.Ep_proj (loc, p, ep), fm ->
        SyntaxPED.Ep_proj (loc, p, rv_ep ep fm)
    | SyntaxPED.Ep_constr (loc, ctor, ep), fm ->
        SyntaxPED.Ep_constr (loc, ctor, rv_ep ep fm)
    | SyntaxPED.Ep_field_access (loc, ep, field), fm ->
        SyntaxPED.Ep_field_access (loc, rv_ep ep fm, field)
    | SyntaxPED.Ep_sizeof (loc, cep), fm ->
        SyntaxPED.Ep_sizeof (loc, rv_cep cep fm)
    | SyntaxPED.Ep_cast (loc, tau, ep), fm ->
        SyntaxPED.Ep_cast (loc, rv_t tau fm, rv_ep ep fm)
    | SyntaxPED.Ep_record (loc, field_ep_list), fm ->
        SyntaxPED.Ep_record
          (loc, Lista.map (fun (f, e) -> (f, rv_ep e fm)) field_ep_list)
    | SyntaxPED.Ep_record_update (loc, ep, field_ep_list), fm ->
        SyntaxPED.Ep_record_update
          (loc, rv_ep ep fm,
            Lista.map (fun (f, e) -> (f, rv_ep e fm)) field_ep_list)
    | SyntaxPED.Ep_let (loc, letbind, ep2), fm ->
        SyntaxPED.Ep_let (loc, rv_letbind letbind fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_let2 (loc, xp, tau, ep1, ep2), fm ->
        SyntaxPED.Ep_let2
          (loc, rv_xp xp fm, rv_t tau fm, rv_ep ep1 fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_if (loc, ep1, ep2, ep3), fm ->
        SyntaxPED.Ep_if (loc, rv_ep ep1 fm, rv_ep ep2 fm, rv_ep ep3 fm)
    | SyntaxPED.Ep_block (loc, ep_list), fm ->
        SyntaxPED.Ep_block (loc, Lista.map (fun e -> rv_ep e fm) ep_list)
    | SyntaxPED.Ep_case (loc, ep, pexpp_list), fm ->
        SyntaxPED.Ep_case
          (loc, rv_ep ep fm, Lista.map (fun p -> rv_pexpp p fm) pexpp_list)
    | SyntaxPED.Ep_assign (loc, lexpp, ep1, ep2), fm ->
        SyntaxPED.Ep_assign (loc, rv_lexpp lexpp fm, rv_ep ep1 fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_return (loc, ep), fm ->
        SyntaxPED.Ep_return (loc, rv_ep ep fm)
    | SyntaxPED.Ep_exit (loc, ep), fm -> SyntaxPED.Ep_exit (loc, rv_ep ep fm)
    | SyntaxPED.Ep_ref (loc, idd), fm -> SyntaxPED.Ep_ref (loc, rv_id idd fm)
    | SyntaxPED.Ep_throw (loc, ep), fm -> SyntaxPED.Ep_throw (loc, rv_ep ep fm)
    | SyntaxPED.Ep_try (loc, ep, pexpp_list), fm ->
        SyntaxPED.Ep_try
          (loc, rv_ep ep fm, Lista.map (fun p -> rv_pexpp p fm) pexpp_list)
    | SyntaxPED.Ep_constraint (loc, cp), fm ->
        SyntaxPED.Ep_constraint (loc, rv_cp cp fm)
    | SyntaxPED.Ep_loop (loc, loop, ep1, ep2), fm ->
        SyntaxPED.Ep_loop (loc, loop, rv_ep ep1 fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_for (loc, idd, ep1, ep2, ep3, order, ep4), fm ->
        SyntaxPED.Ep_for
          (loc, rv_id idd fm, rv_ep ep1 fm, rv_ep ep2 fm, rv_ep ep3 fm, order,
            rv_ep ep4 fm)
    | SyntaxPED.Ep_assert (loc, ep1, ep2), fm ->
        SyntaxPED.Ep_assert (loc, rv_ep ep1 fm, rv_ep ep2 fm)
    | SyntaxPED.Ep_vec (loc, ep_list), fm ->
        SyntaxPED.Ep_vec (loc, Lista.map (fun e -> rv_ep e fm) ep_list)
    | SyntaxPED.Ep_list (loc, ep_list), fm ->
        SyntaxPED.Ep_list (loc, Lista.map (fun e -> rv_ep e fm) ep_list)
    | SyntaxPED.Ep_cons (loc, ep1, ep2), fm ->
        SyntaxPED.Ep_cons (loc, rv_ep ep1 fm, rv_ep ep2 fm)
and rv_pexpp
  x0 fm = match x0, fm with
    SyntaxPED.PEXPp_exp (patp, ep), fm ->
      SyntaxPED.PEXPp_exp (rv_pat patp fm, rv_ep ep fm)
    | SyntaxPED.PEXPp_when (patp, ep1, ep2), fm ->
        SyntaxPED.PEXPp_when (rv_pat patp fm, rv_ep ep1 fm, rv_ep ep2 fm)
and rv_letbind
  (SyntaxPED.LBp_val (loc, patp, ep)) fm =
    SyntaxPED.LBp_val (loc, rv_pat patp fm, rv_ep ep fm);;

let rec mk_new
  s xp =
    (xp ^ "_") ^ Stringa.implode (Utils.string_of_nat (Lista.size_list s));;

let rec pat_id
  = function SyntaxPED.Pp_lit (loc, lit) -> []
    | SyntaxPED.Pp_wild loc -> []
    | SyntaxPED.Pp_as_var (loc, patp, xp) -> pat_id patp
    | SyntaxPED.Pp_typ (loc, tau, patp) -> pat_id patp
    | SyntaxPED.Pp_id (loc, idd) -> [idd]
    | SyntaxPED.Pp_as_typ (loc, patp, tau) -> pat_id patp
    | SyntaxPED.Pp_app (loc, idd, patp_list) -> Lista.maps pat_id patp_list
    | SyntaxPED.Pp_vector (loc, patp_list) -> Lista.maps pat_id patp_list
    | SyntaxPED.Pp_vector_concat (loc, patp_list) -> Lista.maps pat_id patp_list
    | SyntaxPED.Pp_tup (loc, patp_list) -> Lista.maps pat_id patp_list
    | SyntaxPED.Pp_list (loc, patp_list) -> Lista.maps pat_id patp_list
    | SyntaxPED.Pp_cons (loc, patp1, patp2) -> pat_id patp1 @ pat_id patp2
    | SyntaxPED.Pp_string_append (loc, patp_list) ->
        Lista.maps pat_id patp_list;;

let rec unzip3
  = function [] -> ([], ([], []))
    | (x, (y, z)) :: xyzs ->
        (let (xs, (ys, zs)) = unzip3 xyzs in (x :: xs, (y :: ys, z :: zs)));;

let rec b_of_lit = function SyntaxVCT.L_true -> SyntaxVCT.B_bool
                   | SyntaxVCT.L_false -> SyntaxVCT.B_bool
                   | SyntaxVCT.L_num n -> SyntaxVCT.B_int
                   | SyntaxVCT.L_zero -> SyntaxVCT.B_bit
                   | SyntaxVCT.L_one -> SyntaxVCT.B_bit
                   | SyntaxVCT.L_unit -> SyntaxVCT.B_unit
                   | SyntaxVCT.L_string uu -> SyntaxVCT.B_string
                   | SyntaxVCT.L_real uv -> SyntaxVCT.B_real
                   | SyntaxVCT.L_undef -> SyntaxVCT.B_undef;;

let rec mk_fresh_aux
  x0 s2 xp = match x0, s2, xp with [], s2, xp -> xp
    | yp :: s, s2, xp ->
        (let a = (if not ((xp : string) = yp) then xp else mk_new s2 xp) in
          mk_fresh_aux s (yp :: s2) a);;

let rec mk_fresh s xp = mk_fresh_aux s [] xp;;

let rec mk_l_eq_c
  x xa1 = match x, xa1 with
    x, SyntaxVCT.L_bitvec bs ->
      SyntaxVCT.C_conj
        (SyntaxVCT.C_eq
           (SyntaxVCT.CE_uop
              (SyntaxVCT.Len, SyntaxVCT.CE_val (SyntaxVCT.V_var x)),
             SyntaxVCT.CE_val
               (SyntaxVCT.V_lit
                 (SyntaxVCT.L_num
                   (Arith.integer_of_nat (Lista.size_list bs))))),
          SyntaxVCT.C_eq
            (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
              SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_bitvec bs))))
    | x, SyntaxVCT.L_unit ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_unit))
    | x, SyntaxVCT.L_zero ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_zero))
    | x, SyntaxVCT.L_one ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_one))
    | x, SyntaxVCT.L_true ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_true))
    | x, SyntaxVCT.L_false ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false))
    | x, SyntaxVCT.L_num v ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num v)))
    | x, SyntaxVCT.L_string v ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_string v)))
    | x, SyntaxVCT.L_undef ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_undef))
    | x, SyntaxVCT.L_real v ->
        SyntaxVCT.C_eq
          (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
            SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_real v)));;

let rec mk_l_eq_t
  l = SyntaxVCT.T_refined_type
        (SyntaxVCT.VIndex, b_of_lit l, mk_l_eq_c SyntaxVCT.VIndex l);;

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
          (SyntaxVCT.VIndex, b, mk_v_eq_c SyntaxVCT.VIndex v);;

let rec mk_mapping
  s ids =
    Lista.fold
      (fun xp m ->
        (if Lista.member Stringa.equal_literal s xp
          then Finite_Map.fmupd Stringa.equal_literal xp (mk_fresh s xp) m
          else m))
      ids Finite_Map.fmempty;;

let rec freshen_pexp_aux
  s patp ep = (let patid = pat_id patp in
               let mapp = mk_mapping s patid in
               let patpa = rv_pat patp mapp in
               let a = rv_ep ep mapp in
                (patpa, a));;

let rec freshen_ep
  s x1 = match s, x1 with
    s, SyntaxPED.Ep_let (loc2, SyntaxPED.LBp_val (loc1, pat, ep1), ep2) ->
      (let (pat_new, ep2_new) = freshen_pexp_aux s pat ep2 in
        SyntaxPED.Ep_let
          (loc2, SyntaxPED.LBp_val (loc1, pat_new, freshen_ep s ep1),
            freshen_ep
              (Lista.remdups Stringa.equal_literal (s @ pat_id pat_new))
              ep2_new))
    | s, SyntaxPED.Ep_let2 (loc, xp, tau, ep1, ep2) ->
        SyntaxPED.Ep_let2 (loc, xp, tau, freshen_ep s ep1, freshen_ep s ep2)
    | s, SyntaxPED.Ep_case (loc, ep, pexpp_list) ->
        SyntaxPED.Ep_case
          (loc, freshen_ep s ep, Lista.map (freshen_pexpp s) pexpp_list)
    | s, SyntaxPED.Ep_val (loc, v) -> SyntaxPED.Ep_val (loc, v)
    | s, SyntaxPED.Ep_mvar (loc, up) -> SyntaxPED.Ep_mvar (loc, up)
    | s, SyntaxPED.Ep_concat (loc, ep_list) ->
        SyntaxPED.Ep_concat (loc, Lista.map (freshen_ep s) ep_list)
    | s, SyntaxPED.Ep_tuple (loc, ep_list) ->
        SyntaxPED.Ep_tuple (loc, Lista.map (freshen_ep s) ep_list)
    | s, SyntaxPED.Ep_app (loc, fp, ep) ->
        SyntaxPED.Ep_app (loc, fp, freshen_ep s ep)
    | s, SyntaxPED.Ep_bop (loc, bop, ep1, ep2) ->
        SyntaxPED.Ep_bop (loc, bop, freshen_ep s ep1, freshen_ep s ep2)
    | s, SyntaxPED.Ep_uop (loc, uop, ep) ->
        SyntaxPED.Ep_uop (loc, uop, freshen_ep s ep)
    | s, SyntaxPED.Ep_proj (loc, p, ep) ->
        SyntaxPED.Ep_proj (loc, p, freshen_ep s ep)
    | s, SyntaxPED.Ep_constr (loc, ctor, ep) ->
        SyntaxPED.Ep_constr (loc, ctor, freshen_ep s ep)
    | s, SyntaxPED.Ep_field_access (loc, ep, field) ->
        SyntaxPED.Ep_field_access (loc, freshen_ep s ep, field)
    | s, SyntaxPED.Ep_sizeof (loc, cep) -> SyntaxPED.Ep_sizeof (loc, cep)
    | s, SyntaxPED.Ep_cast (loc, tau, ep) ->
        SyntaxPED.Ep_cast (loc, tau, freshen_ep s ep)
    | s, SyntaxPED.Ep_record (loc, field_ep_list) ->
        SyntaxPED.Ep_record
          (loc, Lista.map (fun (f, e) -> (f, freshen_ep s e)) field_ep_list)
    | s, SyntaxPED.Ep_record_update (loc, ep, field_ep_list) ->
        SyntaxPED.Ep_record_update
          (loc, freshen_ep s ep,
            Lista.map (fun (f, e) -> (f, freshen_ep s e)) field_ep_list)
    | s, SyntaxPED.Ep_if (loc, ep1, ep2, ep3) ->
        SyntaxPED.Ep_if
          (loc, freshen_ep s ep1, freshen_ep s ep2, freshen_ep s ep3)
    | s, SyntaxPED.Ep_block (loc, ep_list) ->
        SyntaxPED.Ep_block (loc, Lista.map (freshen_ep s) ep_list)
    | s, SyntaxPED.Ep_assign (loc, lexpp, ep1, ep2) ->
        SyntaxPED.Ep_assign (loc, lexpp, freshen_ep s ep1, freshen_ep s ep2)
    | s, SyntaxPED.Ep_return (loc, ep) ->
        SyntaxPED.Ep_return (loc, freshen_ep s ep)
    | s, SyntaxPED.Ep_exit (loc, ep) -> SyntaxPED.Ep_exit (loc, freshen_ep s ep)
    | s, SyntaxPED.Ep_ref (loc, idd) -> SyntaxPED.Ep_ref (loc, idd)
    | s, SyntaxPED.Ep_throw (loc, ep) ->
        SyntaxPED.Ep_throw (loc, freshen_ep s ep)
    | s, SyntaxPED.Ep_try (loc, ep, pexpp_list) ->
        SyntaxPED.Ep_try
          (loc, freshen_ep s ep, Lista.map (freshen_pexpp s) pexpp_list)
    | s, SyntaxPED.Ep_constraint (loc, cp) -> SyntaxPED.Ep_constraint (loc, cp)
    | s, SyntaxPED.Ep_loop (loc, loop, ep1, ep2) ->
        SyntaxPED.Ep_loop (loc, loop, freshen_ep s ep1, freshen_ep s ep2)
    | s, SyntaxPED.Ep_for (loc, idd, ep1, ep2, ep3, order, ep4) ->
        SyntaxPED.Ep_for
          (loc, idd, freshen_ep s ep1, freshen_ep s ep2, freshen_ep s ep3,
            order, freshen_ep s ep4)
    | s, SyntaxPED.Ep_assert (loc, ep1, ep2) ->
        SyntaxPED.Ep_assert (loc, freshen_ep s ep1, freshen_ep s ep2)
    | s, SyntaxPED.Ep_vec (loc, ep_list) ->
        SyntaxPED.Ep_vec (loc, Lista.map (freshen_ep s) ep_list)
    | s, SyntaxPED.Ep_list (loc, ep_list) ->
        SyntaxPED.Ep_list (loc, Lista.map (freshen_ep s) ep_list)
    | s, SyntaxPED.Ep_cons (loc, ep1, ep2) ->
        SyntaxPED.Ep_cons (loc, freshen_ep s ep1, freshen_ep s ep2)
and freshen_pexpp
  s x1 = match s, x1 with
    s, SyntaxPED.PEXPp_exp (patp, ep) ->
      (let (pat_new, ep_new) = freshen_pexp_aux s patp ep in
        SyntaxPED.PEXPp_exp
          (pat_new,
            freshen_ep
              (Lista.remdups Stringa.equal_literal (s @ pat_id pat_new))
              ep_new))
    | s, SyntaxPED.PEXPp_when (patp, ep1, ep2) ->
        (let (pat_new, ep2_new) = freshen_pexp_aux s patp ep2 in
          SyntaxPED.PEXPp_when
            (pat_new, freshen_ep s ep1,
              freshen_ep
                (Lista.remdups Stringa.equal_literal (s @ pat_id pat_new))
                ep2_new));;

let rec mk_eq_proj
  l x i n =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_proj
            ((Utils.string_lit_of_nat n ^ "X") ^ Utils.string_lit_of_nat i,
              SyntaxVCT.V_var x)));;

let rec mk_proj_eq
  x field =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
        SyntaxVCT.CE_val (SyntaxVCT.V_proj (field, SyntaxVCT.V_var x)));;

let rec c_conj_list
  cs = Lista.fold (fun a b -> SyntaxVCT.C_conj (a, b)) cs SyntaxVCT.C_true;;

let rec mk_record_b_c
  zs fts =
    (let (fbs, cs) =
       Utils.unzip
         (Lista.map (fun (x, a) -> (let (aa, b) = a in aux x aa b))
           (Lista.zip zs fts))
       in
      (SyntaxVCT.B_record fbs, c_conj_list cs));;

let rec mk_vec_len_eq_c
  x bs =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_uop (SyntaxVCT.Len, SyntaxVCT.CE_val (SyntaxVCT.V_var x)),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_lit
            (SyntaxVCT.L_num (Arith.integer_of_nat (Lista.size_list bs)))));;

let rec mk_x_eq_c_tuple
  x xs =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var x),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_tuple (Lista.map (fun a -> SyntaxVCT.V_var a) xs)));;

let rec subst_x_cp x = (fun a xa v -> SyntaxPED.subst_cp v xa a) x;;

end;; (*struct SyntaxUtils*)

module Contexts : sig
  type g_entry = GEPair of SyntaxVCT.bp * SyntaxVCT.cp | GETyp of SyntaxVCT.tau
  val equal_g_entrya : g_entry -> g_entry -> bool
  val equal_g_entry : g_entry HOL.equal
  type ('a, 'b) gamma_ext =
    Gamma_ext of
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap *
        (SyntaxVCT.xp * g_entry) list * (SyntaxVCT.xp * g_entry) list *
        (SyntaxVCT.xp * SyntaxVCT.tau) list *
        (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap *
        (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.xp list *
        SyntaxVCT.tau option * 'b
  val conj : SyntaxVCT.cp list -> SyntaxVCT.cp
  val mapi : (Arith.nat -> 'a -> 'b) -> 'a list -> 'b list
  val n_of : SyntaxVCT.xp -> string
  val gamma_x : ('a, 'b) gamma_ext -> (SyntaxVCT.xp * g_entry) list
  val pp_vp : SyntaxVCT.vp -> string
  val pp_ce : SyntaxVCT.cep -> string
  val pp_cp : SyntaxVCT.cp -> string
  val pp_gep : g_entry -> string
  val x_of : SyntaxVCT.xp -> string
  val pp_G : ('a, unit) gamma_ext -> string
  val zipi : 'a list -> (Arith.nat * 'a) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val lookup : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
  val update : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list
  val gamma_x_update :
    ((SyntaxVCT.xp * g_entry) list -> (SyntaxVCT.xp * g_entry) list) ->
      ('a, 'b) gamma_ext -> ('a, 'b) gamma_ext
  val add_var :
    ('a, unit) gamma_ext -> SyntaxVCT.xp * g_entry -> ('a, unit) gamma_ext
  val iterate :
    Arith.nat ->
      (string, (string list)) Finite_Map.fmap ->
        (string, (string list)) Finite_Map.fmap ->
          (string, (string list)) Finite_Map.fmap
  val unify_b_aux :
    SyntaxVCT.bp -> SyntaxVCT.bp -> ((string * SyntaxVCT.bp) list) option
  val bases_of : ('a * SyntaxVCT.tau) list -> SyntaxVCT.bp list
  val unify_b :
    SyntaxVCT.bp -> SyntaxVCT.bp -> ((string * SyntaxVCT.bp) list) option
  val unify_b_list :
    SyntaxVCT.bp list ->
      SyntaxVCT.bp list -> ((string * SyntaxVCT.bp) list) option
  val add_vars :
    ('a, unit) gamma_ext ->
      (SyntaxVCT.xp * g_entry) list -> ('a, unit) gamma_ext
  val emptyEnv : ('a, unit) gamma_ext
  val gamma_f :
    ('a, 'b) gamma_ext ->
      (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
        Finite_Map.fmap
  val check_var : ('a, unit) gamma_ext -> SyntaxVCT.xp -> bool
  val mk_ctor_v : string -> SyntaxVCT.xp list -> SyntaxVCT.vp
  val subst_c_x : SyntaxVCT.cp -> SyntaxVCT.xp -> SyntaxVCT.cp
  val check_vars : ('a, unit) gamma_ext -> SyntaxVCT.xp list -> bool
  val convert_ge :
    (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
      (SyntaxVCT.xp * g_entry) list
  val lookup_ivar : ('a, unit) gamma_ext -> SyntaxVCT.xp -> g_entry option
  val lookup_var : ('a, unit) gamma_ext -> SyntaxVCT.xp -> g_entry option
  val subst_c_v0 : SyntaxVCT.cp -> SyntaxVCT.vp -> SyntaxVCT.cp
  val tuple_proj : Arith.nat -> Arith.nat -> SyntaxVCT.vp -> SyntaxVCT.vp
  val add_vars_ge :
    ('a, unit) gamma_ext ->
      (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
        ('a, unit) gamma_ext
  val remove_tick : string -> string
  val single_base : SyntaxVCT.bp list -> SyntaxVCT.bp option
  val gamma_s_update :
    (SyntaxVCT.xp list -> SyntaxVCT.xp list) ->
      ('a, 'b) gamma_ext -> ('a, 'b) gamma_ext
  val gamma_s : ('a, 'b) gamma_ext -> SyntaxVCT.xp list
  val add_to_scope :
    ('a, unit) gamma_ext -> SyntaxVCT.xp list -> ('a, unit) gamma_ext
  val lookup_scope : ('a, unit) gamma_ext -> SyntaxVCT.xp -> bool
  val convert_to_bc :
    Arith.nat -> Arith.nat -> SyntaxVCT.tau -> SyntaxVCT.bp * SyntaxVCT.cp
  val convert_to_st : SyntaxVCT.tau list -> SyntaxVCT.bp list * SyntaxVCT.cp
  val add_type_to_scope :
    ('a, unit) gamma_ext -> SyntaxVCT.tau -> ('a, unit) gamma_ext
  val gamma_e : ('a, 'b) gamma_ext -> SyntaxVCT.tau option
  val gamma_u : ('a, 'b) gamma_ext -> (SyntaxVCT.xp * g_entry) list
  val gamma_e_update :
    (SyntaxVCT.tau option -> SyntaxVCT.tau option) ->
      ('a, 'b) gamma_ext -> ('a, 'b) gamma_ext
end = struct

type g_entry = GEPair of SyntaxVCT.bp * SyntaxVCT.cp | GETyp of SyntaxVCT.tau;;

let rec equal_g_entrya
  x0 x1 = match x0, x1 with GEPair (x11, x12), GETyp x2 -> false
    | GETyp x2, GEPair (x11, x12) -> false
    | GETyp x2, GETyp y2 -> SyntaxVCT.equal_taua x2 y2
    | GEPair (x11, x12), GEPair (y11, y12) ->
        SyntaxVCT.equal_bpa x11 y11 && SyntaxVCT.equal_cpa x12 y12;;

let equal_g_entry = ({HOL.equal = equal_g_entrya} : g_entry HOL.equal);;

type ('a, 'b) gamma_ext =
  Gamma_ext of
    (SyntaxVCT.xp, ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list))
      Finite_Map.fmap *
      (SyntaxVCT.xp * g_entry) list * (SyntaxVCT.xp * g_entry) list *
      (SyntaxVCT.xp * SyntaxVCT.tau) list *
      (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap *
      (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.xp list *
      SyntaxVCT.tau option * 'b;;

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

let rec n_of = function SyntaxVCT.VNamed s -> s
               | SyntaxVCT.VIndex -> "#0";;

let rec gamma_x
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
      more))
    = gamma_x;;

let rec pp_vp = function SyntaxVCT.V_var (SyntaxVCT.VNamed s) -> s
                | SyntaxVCT.V_lit v -> "vp"
                | SyntaxVCT.V_var SyntaxVCT.VIndex -> "vp"
                | SyntaxVCT.V_vec v -> "vp"
                | SyntaxVCT.V_list v -> "vp"
                | SyntaxVCT.V_cons (v, va) -> "vp"
                | SyntaxVCT.V_constr (v, va) -> "vp"
                | SyntaxVCT.V_record v -> "vp"
                | SyntaxVCT.V_tuple v -> "vp"
                | SyntaxVCT.V_proj (v, va) -> "vp";;

let rec pp_ce
  = function SyntaxVCT.CE_val v -> pp_vp v
    | SyntaxVCT.CE_bop (SyntaxVCT.Plus, e1, e2) -> (pp_ce e1 ^ " + ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.LEq, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Times, e1, e2) ->
        (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Minus, e1, e2) ->
        (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Div, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Mod, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Eq, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.NEq, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.LT, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.And, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.Or, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.GEq, e1, e2) -> (pp_ce e1 ^ "GEq") ^ pp_ce e2
    | SyntaxVCT.CE_bop (SyntaxVCT.GT, e1, e2) -> (pp_ce e1 ^ " <= ") ^ pp_ce e2
    | SyntaxVCT.CE_uop (SyntaxVCT.Len, e) -> pp_ce e
    | SyntaxVCT.CE_uop (SyntaxVCT.Nott, e) -> pp_ce e
    | SyntaxVCT.CE_uop (SyntaxVCT.Abs, e) -> pp_ce e
    | SyntaxVCT.CE_many_plus v -> failwith "undefined"
    | SyntaxVCT.CE_uop (SyntaxVCT.Exp, va) -> pp_ce va
    | SyntaxVCT.CE_uop (SyntaxVCT.Neg, va) -> pp_ce va
    | SyntaxVCT.CE_proj (v, va) -> pp_ce va
    | SyntaxVCT.CE_field_access (vp, field) -> pp_vp vp;;

let rec pp_cp = function SyntaxVCT.C_true -> "T"
                | SyntaxVCT.C_false -> "F"
                | SyntaxVCT.C_conj (c1, c2) -> (pp_cp c1 ^ " AND ") ^ pp_cp c2
                | SyntaxVCT.C_disj (c1, c2) -> (pp_cp c1 ^ " OR  ") ^ pp_cp c2
                | SyntaxVCT.C_not c -> pp_cp c
                | SyntaxVCT.C_imp (c1, c2) -> pp_cp c1 ^ pp_cp c2
                | SyntaxVCT.C_eq (e1, e2) -> (pp_ce e1 ^ "=") ^ pp_ce e2
                | SyntaxVCT.C_leq (e1, e2) -> "C_leq"
                | SyntaxVCT.C_conj_many cs -> "C_conj_many";;

let rec pp_gep (GEPair (bp, cp)) = pp_cp cp;;

let rec x_of (SyntaxVCT.VNamed x) = x;;

let rec pp_G
  g = Stringa.implode
        (Lista.maps
          (fun (x, gep) ->
            Stringa.explode (((x_of x ^ "[ ") ^ pp_gep gep) ^ "]"))
          (gamma_x g));;

let rec zipi xs = mapi (fun a b -> (a, b)) xs;;

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
      (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
        more))
    = Gamma_ext
        (gamma_f, gamma_xa gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s,
          gamma_e, more);;

let rec add_var
  gamma (x, t) = gamma_x_update (fun _ -> (x, t) :: gamma_x gamma) gamma;;

let rec iterate
  i fm1 fm2 =
    (if Arith.equal_nat i Arith.zero_nat then fm2
      else Finite_Map.fmmap_keys
             (fun _ ss1 ->
               Lista.remdups Stringa.equal_literal
                 (ss1 @
                   Lista.maps
                     (fun s ->
                       (match Finite_Map.fmlookup Stringa.equal_literal fm1 s
                         with None -> [] | Some ss -> ss))
                     ss1))
             (iterate (Arith.minus_nat i Arith.one_nat) fm1 fm2));;

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
    | uu, SyntaxVCT.B_reg v -> None
    | uu, SyntaxVCT.B_string -> None
    | uu, SyntaxVCT.B_exception -> None
    | uu, SyntaxVCT.B_finite_set v -> None;;

let rec bases_of
  ts = Lista.map (Fun.comp SyntaxUtils.b_of Product_Type.snd) ts;;

let rec unify_b
  b1 b2 = match b1, b2 with
    SyntaxVCT.B_vec (o1, b1), SyntaxVCT.B_vec (o2, b2) ->
      (if SyntaxVCT.equal_order o1 o2
        then (match unify_b b1 b2 with None -> None | Some a -> Some a)
        else None)
    | SyntaxVCT.B_list b1, SyntaxVCT.B_list b2 ->
        (match unify_b b1 b2 with None -> None | Some a -> Some a)
    | SyntaxVCT.B_union (s1, ts1), SyntaxVCT.B_union (s2, ts2) ->
        unify_b_list (bases_of ts1) (bases_of ts2)
    | SyntaxVCT.B_tuple bs1, SyntaxVCT.B_tuple bs2 -> unify_b_list bs1 bs2
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
    | SyntaxVCT.B_list v, SyntaxVCT.B_reg va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_list v) (SyntaxVCT.B_reg va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_list v) (SyntaxVCT.B_reg va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_reg va) (SyntaxVCT.B_list v)
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
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_var va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_var va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_var va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_var va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_tid va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_tid va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_tid va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tid va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_int ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_int
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_int
                 with None -> unify_b_aux SyntaxVCT.B_int (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_bool ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_bool
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_bool
                 with None -> unify_b_aux SyntaxVCT.B_bool (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_bit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_bit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_bit
                 with None -> unify_b_aux SyntaxVCT.B_bit (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_unit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_unit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_unit
                 with None -> unify_b_aux SyntaxVCT.B_unit (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_real ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_real
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_real
                 with None -> unify_b_aux SyntaxVCT.B_real (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_vec (va, vb) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_vec (va, vb))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_vec (va, vb))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_list va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_list va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_list va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_list va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_union (va, vb) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v)
              (SyntaxVCT.B_union (va, vb))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_union (va, vb))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_union (va, vb))
                     (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_record va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_record va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_record va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_record va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_undef ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_undef
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_undef
                 with None ->
                   unify_b_aux SyntaxVCT.B_undef (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_reg va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) (SyntaxVCT.B_reg va)
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_reg va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_reg va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_string ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_string
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_string
                 with None ->
                   unify_b_aux SyntaxVCT.B_string (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_exception ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v) SyntaxVCT.B_exception
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_tuple v) SyntaxVCT.B_exception
                 with None ->
                   unify_b_aux SyntaxVCT.B_exception (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_tuple v, SyntaxVCT.B_finite_set va ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_tuple v)
              (SyntaxVCT.B_finite_set va)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_finite_set va)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_finite_set va) (SyntaxVCT.B_tuple v)
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_var vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_var vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_var vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_var vb) (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_tid vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_tid vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_tid vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tid vb) (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_int ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_int
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_int
                 with None ->
                   unify_b_aux SyntaxVCT.B_int (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_bool ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_bool
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_bool
                 with None ->
                   unify_b_aux SyntaxVCT.B_bool (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_bit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_bit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_bit
                 with None ->
                   unify_b_aux SyntaxVCT.B_bit (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_unit ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_unit
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_unit
                 with None ->
                   unify_b_aux SyntaxVCT.B_unit (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_real ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_real
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_real
                 with None ->
                   unify_b_aux SyntaxVCT.B_real (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_vec (vb, vc) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              (SyntaxVCT.B_vec (vb, vc))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va))
                   (SyntaxVCT.B_vec (vb, vc))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_vec (vb, vc))
                     (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_list vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              (SyntaxVCT.B_list vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_list vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_list vb) (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_tuple vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              (SyntaxVCT.B_tuple vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_tuple vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tuple vb)
                     (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_record vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              (SyntaxVCT.B_record vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_record vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_record vb)
                     (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_undef ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_undef
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_undef
                 with None ->
                   unify_b_aux SyntaxVCT.B_undef (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_reg vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_reg vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) (SyntaxVCT.B_reg vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_reg vb) (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_string ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_string
          then Some []
          else (match unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_string
                 with None ->
                   unify_b_aux SyntaxVCT.B_string (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_exception ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              SyntaxVCT.B_exception
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va)) SyntaxVCT.B_exception
                 with None ->
                   unify_b_aux SyntaxVCT.B_exception (SyntaxVCT.B_union (v, va))
                 | Some a -> Some a))
    | SyntaxVCT.B_union (v, va), SyntaxVCT.B_finite_set vb ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_union (v, va))
              (SyntaxVCT.B_finite_set vb)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_union (v, va))
                   (SyntaxVCT.B_finite_set vb)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_finite_set vb)
                     (SyntaxVCT.B_union (v, va))
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
    | SyntaxVCT.B_reg v, b2 ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_reg v) b2 then Some []
          else (match unify_b_aux (SyntaxVCT.B_reg v) b2
                 with None -> unify_b_aux b2 (SyntaxVCT.B_reg v)
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
    | SyntaxVCT.B_vec (va, vb), SyntaxVCT.B_tuple v ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_tuple v)
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_vec (va, vb)) (SyntaxVCT.B_tuple v)
                 with None ->
                   unify_b_aux (SyntaxVCT.B_tuple v) (SyntaxVCT.B_vec (va, vb))
                 | Some a -> Some a))
    | SyntaxVCT.B_vec (vb, vc), SyntaxVCT.B_union (v, va) ->
        (if SyntaxVCT.equal_bpa (SyntaxVCT.B_vec (vb, vc))
              (SyntaxVCT.B_union (v, va))
          then Some []
          else (match
                 unify_b_aux (SyntaxVCT.B_vec (vb, vc))
                   (SyntaxVCT.B_union (v, va))
                 with None ->
                   unify_b_aux (SyntaxVCT.B_union (v, va))
                     (SyntaxVCT.B_vec (vb, vc))
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
    | b1, SyntaxVCT.B_reg v ->
        (if SyntaxVCT.equal_bpa b1 (SyntaxVCT.B_reg v) then Some []
          else (match unify_b_aux b1 (SyntaxVCT.B_reg v)
                 with None -> unify_b_aux (SyntaxVCT.B_reg v) b1
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
                 | Some a -> Some a))
and unify_b_list
  x0 x1 = match x0, x1 with
    t1 :: ts1, t2 :: ts2 ->
      (match unify_b t1 t2 with None -> None
        | Some bs ->
          (match unify_b_list ts1 ts2 with None -> None
            | Some bs2 -> Some (bs @ bs2)))
    | [], [] -> Some []
    | [], v :: va -> None
    | v :: va, [] -> None;;

let rec add_vars gamma bs = gamma_x_update (fun _ -> bs @ gamma_x gamma) gamma;;

let emptyEnv : ('a, unit) gamma_ext
  = Gamma_ext
      (Finite_Map.fmempty, [], [], [], Finite_Map.fmempty, Finite_Map.fmempty,
        [], None, ());;

let rec gamma_f
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
      more))
    = gamma_f;;

let rec check_var
  g x = (match Finite_Map.fmlookup SyntaxVCT.equal_xp (gamma_f g) x
          with None -> true | Some _ -> false);;

let rec mk_ctor_v
  idx x1 = match idx, x1 with
    idx, [x] -> SyntaxVCT.V_constr (idx, SyntaxVCT.V_var x)
    | idx, [] -> SyntaxVCT.V_constr (idx, SyntaxVCT.V_tuple [])
    | idx, x :: v :: va ->
        SyntaxVCT.V_constr
          (idx, SyntaxVCT.V_tuple
                  (Lista.map (fun a -> SyntaxVCT.V_var a) (x :: v :: va)));;

let rec subst_c_x
  c x = SyntaxPED.subst_cp (SyntaxVCT.V_var x) SyntaxVCT.VIndex c;;

let rec check_vars g xs = Lista.list_all (check_var g) xs;;

let rec convert_ge xs = Lista.map (fun (x, (b, c)) -> (x, GEPair (b, c))) xs;;

let rec lookup_ivar gamma x = lookup SyntaxVCT.equal_xp (gamma_x gamma) x;;

let rec lookup_var gamma x = lookup_ivar gamma x;;

let rec subst_c_v0 c v = SyntaxPED.subst_cp v SyntaxVCT.VIndex c;;

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

let rec remove_tick
  y = (match Stringa.explode y with [] -> y
        | x :: xs ->
          (if Stringa.equal_char x
                (Stringa.Chara
                  (true, true, true, false, false, true, false, false))
            then Stringa.implode xs else y));;

let rec single_base
  = function [] -> None
    | b :: bs ->
        (if Lista.list_all (SyntaxVCT.equal_bpa b) bs then Some b else None);;

let rec gamma_s_update
  gamma_sa
    (Gamma_ext
      (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
        more))
    = Gamma_ext
        (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_sa gamma_s,
          gamma_e, more);;

let rec gamma_s
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
      more))
    = gamma_s;;

let rec add_to_scope
  gamma xs = gamma_s_update (fun _ -> xs @ gamma_s gamma) gamma;;

let rec lookup_scope
  gamma x = Lista.member SyntaxVCT.equal_xp (gamma_s gamma) x;;

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

let rec add_type_to_scope
  gamma x1 = match gamma, x1 with
    gamma,
      SyntaxVCT.T_refined_type (zvar, SyntaxVCT.B_union (uname, variants), c)
      -> add_to_scope gamma
           (Lista.map (fun s -> SyntaxVCT.VNamed (Product_Type.fst s)) variants)
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_var vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tid vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_int, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bool, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_bit, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_unit, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_real, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_vec (vc, vd), vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_list vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_tuple vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_record vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_undef, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb) -> gamma
    | gamma, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb) ->
        gamma;;

let rec gamma_e
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
      more))
    = gamma_e;;

let rec gamma_u
  (Gamma_ext
    (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
      more))
    = gamma_u;;

let rec gamma_e_update
  gamma_ea
    (Gamma_ext
      (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s, gamma_e,
        more))
    = Gamma_ext
        (gamma_f, gamma_x, gamma_u, gamma_T, gamma_o, gamma_r, gamma_s,
          gamma_ea gamma_e, more);;

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
      (SyntaxVCT.xp * SyntaxVCT.tau) list *
        (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.order option *
        'a
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
  val b_of_ge : Contexts.g_entry -> SyntaxVCT.bp
  val delta_m_update :
    ((string * SyntaxVCT.tau) list -> (string * SyntaxVCT.tau) list) ->
      'a delta_ext -> 'a delta_ext
  val delta_m : 'a delta_ext -> (string * SyntaxVCT.tau) list
  val add_mvar : unit delta_ext -> string * SyntaxVCT.tau -> unit delta_ext
  val theta_T_update :
    ((SyntaxVCT.xp * SyntaxVCT.tau) list ->
      (SyntaxVCT.xp * SyntaxVCT.tau) list) ->
      'a theta_ext -> 'a theta_ext
  val theta_T : 'a theta_ext -> (SyntaxVCT.xp * SyntaxVCT.tau) list
  val add_to_scope_theta : unit theta_ext -> SyntaxVCT.xp list -> unit theta_ext
  val add_type :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau -> unit theta_ext
  val emptyDEnv : unit delta_ext
  val lookup_field_in_type : SyntaxVCT.tau -> string -> SyntaxVCT.bp option
  val lookup_field_record_aux :
    (SyntaxVCT.xp * SyntaxVCT.tau) list ->
      string -> (SyntaxVCT.xp * SyntaxVCT.tau) option
  val lookup_field_record :
    unit theta_ext -> string -> (SyntaxVCT.xp * SyntaxVCT.tau) option
  val lookup_record_name : unit theta_ext -> string -> string option
  val tids_in_b_aux : unit theta_ext -> SyntaxVCT.bp -> string list
  val tids_in_t_aux : unit theta_ext -> SyntaxVCT.tau -> string list
  val tids_in_b : unit theta_ext -> SyntaxVCT.bp -> string list
  val tids_in_t : unit theta_ext -> SyntaxVCT.tau -> string list
  val fm_from_t : unit theta_ext -> (string, (string list)) Finite_Map.fmap
  val emptyPiEnv : ('a, unit) phi_ext
  val restrict_t :
    (SyntaxVCT.xp * SyntaxVCT.tau) list ->
      string list -> (SyntaxVCT.xp * SyntaxVCT.tau) list
  val lookup_mvar : unit delta_ext -> string -> SyntaxVCT.tau option
  val minimise_td :
    unit theta_ext ->
      (SyntaxVCT.xp * Contexts.g_entry) list ->
        (SyntaxVCT.xp * SyntaxVCT.tau) list
  val update_mvar : unit delta_ext -> string * SyntaxVCT.tau -> unit delta_ext
  val update_type :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau -> unit theta_ext
  val theta_r_update :
    ((SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap ->
      (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap) ->
      'a theta_ext -> 'a theta_ext
  val theta_r : 'a theta_ext -> (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap
  val add_register :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau -> unit theta_ext
  val emptyThetaEnv : unit theta_ext
  val lookup_fields : unit theta_ext -> string list -> SyntaxVCT.tau option
  val mvar_not_in_d : unit delta_ext -> string -> bool
  val phi_o :
    ('a, 'b) phi_ext -> (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap
  val lookup_fun_aux :
    ('a, unit) phi_ext ->
      SyntaxVCT.xp -> ((SyntaxVCT.xp * (SyntaxVCT.ap * 'a option)) list) option
  val phi_o_update :
    ((SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap ->
      (SyntaxVCT.xp, (SyntaxVCT.xp list)) Finite_Map.fmap) ->
      ('a, 'b) phi_ext -> ('a, 'b) phi_ext
  val add_to_overload :
    ('a, unit) phi_ext ->
      SyntaxVCT.xp -> SyntaxVCT.xp list -> ('a, unit) phi_ext
  val lookup_register : unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau option
  val lookup_types_for :
    SyntaxVCT.bp -> string list -> (SyntaxVCT.bp list) option
  val lookup_constr_in_type : SyntaxVCT.tau -> string -> SyntaxVCT.tau option
  val lookup_constr_aux :
    (SyntaxVCT.xp * SyntaxVCT.tau) list -> string -> SyntaxVCT.tau option
  val lookup_constr_union : unit theta_ext -> string -> SyntaxVCT.tau option
  val lookup_constr_union_x :
    unit theta_ext -> SyntaxVCT.xp -> SyntaxVCT.tau option
  val lookup_constr_union_type :
    unit theta_ext -> string -> (SyntaxVCT.tau * SyntaxVCT.tau) option
  val lookup_field_record_type :
    unit theta_ext -> string -> (SyntaxVCT.bp * SyntaxVCT.tau) option
  val theta_d : 'a theta_ext -> SyntaxVCT.order option
  val lookup_field_and_record_type :
    unit theta_ext -> string -> (SyntaxVCT.tau * SyntaxVCT.tau) option
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
    (SyntaxVCT.xp * SyntaxVCT.tau) list *
      (SyntaxVCT.xp, SyntaxVCT.tau) Finite_Map.fmap * SyntaxVCT.order option *
      'a;;

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

let rec b_of_ge (Contexts.GEPair (b, c)) = b;;

let rec delta_m_update
  delta_ma (Delta_ext (delta_m, more)) = Delta_ext (delta_ma delta_m, more);;

let rec delta_m (Delta_ext (delta_m, more)) = delta_m;;

let rec add_mvar
  delta (x, t) =
    (match Contexts.lookup Stringa.equal_literal (delta_m delta) x
      with None ->
        delta_m_update
          (fun _ -> Contexts.update Stringa.equal_literal (delta_m delta) x t)
          delta
      | Some _ -> delta);;

let rec theta_T_update
  theta_Ta (Theta_ext (theta_T, theta_r, theta_d, more)) =
    Theta_ext (theta_Ta theta_T, theta_r, theta_d, more);;

let rec theta_T (Theta_ext (theta_T, theta_r, theta_d, more)) = theta_T;;

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
    | phi, x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb) ->
        theta_T_update
          (fun _ ->
            (x, SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb)) ::
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
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb), uw -> None
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

let rec tids_in_b_aux
  t x1 = match t, x1 with t, SyntaxVCT.B_tid i -> [i]
    | t, SyntaxVCT.B_tuple bs -> Lista.maps (tids_in_b_aux t) bs
    | t, SyntaxVCT.B_record ((fid, uu) :: xs) ->
        (match lookup_record_name t fid with None -> [] | Some s -> [s])
    | t, SyntaxVCT.B_union (i, vs) -> [i]
    | t, SyntaxVCT.B_var v -> []
    | t, SyntaxVCT.B_int -> []
    | t, SyntaxVCT.B_bool -> []
    | t, SyntaxVCT.B_bit -> []
    | t, SyntaxVCT.B_unit -> []
    | t, SyntaxVCT.B_real -> []
    | t, SyntaxVCT.B_vec (v, va) -> []
    | t, SyntaxVCT.B_list v -> []
    | t, SyntaxVCT.B_record [] -> []
    | t, SyntaxVCT.B_undef -> []
    | t, SyntaxVCT.B_reg v -> []
    | t, SyntaxVCT.B_string -> []
    | t, SyntaxVCT.B_exception -> []
    | t, SyntaxVCT.B_finite_set v -> [];;

let rec tids_in_t_aux ta t = tids_in_b_aux ta (SyntaxUtils.b_of t);;

let rec tids_in_b
  t x1 = match t, x1 with t, SyntaxVCT.B_tid i -> [i]
    | t, SyntaxVCT.B_tuple bs -> Lista.maps (tids_in_b_aux t) bs
    | t, SyntaxVCT.B_record ((fid, uu) :: xs) ->
        (match lookup_record_name t fid with None -> [] | Some s -> [s])
    | t, SyntaxVCT.B_union (i, vs) ->
        i :: Lista.maps (Fun.comp (tids_in_t_aux t) Product_Type.snd) vs
    | t, SyntaxVCT.B_var v -> []
    | t, SyntaxVCT.B_int -> []
    | t, SyntaxVCT.B_bool -> []
    | t, SyntaxVCT.B_bit -> []
    | t, SyntaxVCT.B_unit -> []
    | t, SyntaxVCT.B_real -> []
    | t, SyntaxVCT.B_vec (v, va) -> []
    | t, SyntaxVCT.B_list v -> []
    | t, SyntaxVCT.B_record [] -> []
    | t, SyntaxVCT.B_undef -> []
    | t, SyntaxVCT.B_reg v -> []
    | t, SyntaxVCT.B_string -> []
    | t, SyntaxVCT.B_exception -> []
    | t, SyntaxVCT.B_finite_set v -> [];;

let rec tids_in_t ta t = tids_in_b ta (SyntaxUtils.b_of t);;

let rec fm_from_t
  t = Finite_Map.Fmap_of_list
        (Lista.map (fun (s, ta) -> (Contexts.n_of s, tids_in_t t ta))
          (theta_T t));;

let emptyPiEnv : ('a, unit) phi_ext
  = Phi_ext (Finite_Map.fmempty, Finite_Map.fmempty, ());;

let rec restrict_t
  x0 uu = match x0, uu with [], uu -> []
    | (xp, ta) :: t, ss ->
        (if Lista.member Stringa.equal_literal ss (Contexts.n_of xp)
          then (xp, ta) :: restrict_t t ss else restrict_t t ss);;

let rec lookup_mvar
  delta x = Contexts.lookup Stringa.equal_literal (delta_m delta) x;;

let rec minimise_td
  t g = (let fm = fm_from_t t in
         let fma = Contexts.iterate (Lista.size_list (theta_T t)) fm fm in
         let bps = Lista.map (fun (_, a) -> b_of_ge a) g in
         let ss_bp =
           Lista.remdups Stringa.equal_literal (Lista.maps (tids_in_b t) bps) in
         let ss =
           Lista.remdups Stringa.equal_literal
             (Lista.maps
               (fun s ->
                 (match Finite_Map.fmlookup Stringa.equal_literal fma s
                   with None -> [] | Some ss -> ss))
               ss_bp)
           in
          restrict_t (theta_T t)
            (Lista.remdups Stringa.equal_literal (ss @ ss_bp)));;

let rec update_mvar
  delta (x, t) =
    delta_m_update
      (fun _ -> Contexts.update Stringa.equal_literal (delta_m delta) x t)
      delta;;

let rec update_type
  theta x t =
    theta_T_update
      (fun _ -> Contexts.update SyntaxVCT.equal_xp (theta_T theta) x t) theta;;

let rec theta_r_update
  theta_ra (Theta_ext (theta_T, theta_r, theta_d, more)) =
    Theta_ext (theta_T, theta_ra theta_r, theta_d, more);;

let rec theta_r (Theta_ext (theta_T, theta_r, theta_d, more)) = theta_r;;

let rec add_register
  theta xp t =
    theta_r_update
      (fun _ -> Finite_Map.fmupd SyntaxVCT.equal_xp xp t (theta_r theta))
      theta;;

let emptyThetaEnv : unit theta_ext
  = Theta_ext ([], Finite_Map.fmempty, None, ());;

let rec lookup_fields
  g x1 = match g, x1 with
    g, fid :: uu ->
      (match lookup_field_record g fid with None -> None
        | Some a -> (let (_, aa) = a in Some aa))
    | g, [] -> None;;

let rec mvar_not_in_d
  delta x =
    (match Contexts.lookup Stringa.equal_literal (delta_m delta) x
      with None -> true | Some _ -> false);;

let rec phi_o (Phi_ext (phi_f, phi_o, more)) = phi_o;;

let rec lookup_fun_aux
  phi x =
    (match Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_o phi) x
      with None -> Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_f phi) x
      | Some xs ->
        Some (Lista.concat
               (Lista.map_filter
                 (Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_f phi)) xs)));;

let rec phi_o_update
  phi_oa (Phi_ext (phi_f, phi_o, more)) = Phi_ext (phi_f, phi_oa phi_o, more);;

let rec add_to_overload
  phi idd id_list =
    (match Finite_Map.fmlookup SyntaxVCT.equal_xp (phi_o phi) idd
      with None ->
        phi_o_update
          (fun _ -> Finite_Map.fmupd SyntaxVCT.equal_xp idd id_list (phi_o phi))
          phi
      | Some id_lista ->
        phi_o_update
          (fun _ ->
            Finite_Map.fmupd SyntaxVCT.equal_xp idd (id_lista @ id_list)
              (phi_o phi))
          phi);;

let rec lookup_register
  t x = Finite_Map.fmlookup SyntaxVCT.equal_xp (theta_r t) x;;

let rec lookup_types_for
  x0 uw = match x0, uw with
    SyntaxVCT.B_record fbs, f :: fs ->
      (match lookup_types_for (SyntaxVCT.B_record fbs) fs with None -> None
        | Some bp ->
          (match Contexts.lookup Stringa.equal_literal fbs f with None -> None
            | Some b -> Some (b :: bp)))
    | SyntaxVCT.B_record uu, [] -> Some []
    | SyntaxVCT.B_var v, uw -> None
    | SyntaxVCT.B_tid v, uw -> None
    | SyntaxVCT.B_int, uw -> None
    | SyntaxVCT.B_bool, uw -> None
    | SyntaxVCT.B_bit, uw -> None
    | SyntaxVCT.B_unit, uw -> None
    | SyntaxVCT.B_real, uw -> None
    | SyntaxVCT.B_vec (v, va), uw -> None
    | SyntaxVCT.B_list v, uw -> None
    | SyntaxVCT.B_tuple v, uw -> None
    | SyntaxVCT.B_union (v, va), uw -> None
    | SyntaxVCT.B_undef, uw -> None
    | SyntaxVCT.B_reg v, uw -> None
    | SyntaxVCT.B_string, uw -> None
    | SyntaxVCT.B_exception, uw -> None
    | SyntaxVCT.B_finite_set v, uw -> None;;

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
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_reg vc, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_string, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_exception, vb), uw -> None
    | SyntaxVCT.T_refined_type (v, SyntaxVCT.B_finite_set vc, vb), uw -> None;;

let rec lookup_constr_aux
  x0 uu = match x0, uu with [], uu -> None
    | (xa, t) :: ts, x ->
        (match lookup_constr_in_type t x with None -> lookup_constr_aux ts x
          | Some _ -> Some t);;

let rec lookup_constr_union theta fid = lookup_constr_aux (theta_T theta) fid;;

let rec lookup_constr_union_x g (SyntaxVCT.VNamed x) = lookup_constr_union g x;;

let rec lookup_constr_union_type
  phi fid =
    (match lookup_constr_union phi fid with None -> None
      | Some t1 ->
        (match lookup_constr_in_type t1 fid with None -> None
          | Some t2 -> Some (t1, t2)));;

let rec lookup_field_record_type
  theta fid =
    (match lookup_field_record theta fid with None -> None
      | Some (_, t) ->
        (match lookup_field_in_type t fid with None -> None
          | Some ta -> Some (ta, t)));;

let rec theta_d (Theta_ext (theta_T, theta_r, theta_d, more)) = theta_d;;

let rec lookup_field_and_record_type
  theta fid =
    (match lookup_field_record theta fid with None -> None
      | Some (_, t) ->
        (match lookup_field_in_type t fid with None -> None
          | Some ta ->
            Some (SyntaxVCT.T_refined_type
                    (SyntaxVCT.VIndex, ta, SyntaxVCT.C_true),
                   t)));;

let rec theta_d_update
  theta_da (Theta_ext (theta_T, theta_r, theta_d, more)) =
    Theta_ext (theta_T, theta_r, theta_da theta_d, more);;

end;; (*struct ContextsPiDelta*)

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
  val map2M : ('a -> 'b -> 'c checkM) -> 'a list -> 'b list -> ('c list) checkM
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
  val get_state : unit -> state checkM
  val set_state : state -> unit checkM
  val lookup_fun :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        SyntaxVCT.xp ->
          ((SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list) option
  val convert_fun :
    SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option) ->
      (SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) checkM
  val subst_e_list :
    SyntaxPED.ep -> (SyntaxVCT.xp * SyntaxVCT.vp) list -> SyntaxPED.ep
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

let rec map2M
  uu x1 uv = match uu, x1, uv with uu, [], uv -> return []
    | uw, v :: va, [] -> return []
    | f, x :: xs, y :: ys ->
        check_bind (f x y)
          (fun xy ->
            check_bind (map2M f xs ys) (fun xys -> return (xy :: xys)));;

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
              StateD (Arith.plus_int i Arith.one_inta, w)));;

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

let rec get_state uu = State (fun s -> (Check_Ok s, s));;

let rec set_state s = State (fun a -> (Check_Ok (), a));;

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

let rec subst_e_list
  c x1 = match c, x1 with c, [] -> c
    | c, (x, v) :: xvs -> subst_e_list (SyntaxPED.subst_ep v x c) xvs;;

let rec lookup_fun_and_convert_aux
  t pi f =
    (match lookup_fun t pi f with None -> return []
      | Some a -> mapM convert_fun a);;

end;; (*struct Monad*)


module Predicate : sig
  type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  and 'a pred = Seq of (unit -> 'a seq)
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val adjunct : 'a pred -> 'a seq -> 'a seq
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
  val set_of_seq : 'a HOL.equal -> 'a seq -> 'a Set.set
  val set_of_pred : 'a HOL.equal -> 'a pred -> 'a Set.set
end = struct

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
                  | p, Insert (x, q) -> Insert (x, sup_pred q p)
                  | p, Join (q, xq) -> Join (q, adjunct p xq)
and sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))));;

let rec if_pred b = (if b then single () else bot_pred);;

let rec set_of_seq _A
  = function
    Join (p, xq) -> Set.sup_set _A (set_of_pred _A p) (set_of_seq _A xq)
    | Insert (x, p) -> Set.insert _A x (set_of_pred _A p)
    | Empty -> Set.bot_set
and set_of_pred _A
  (Seq f) =
    (match f () with Empty -> Set.bot_set
      | Insert (x, p) -> Set.insert _A x (set_of_pred _A p)
      | Join (p, xq) -> Set.sup_set _A (set_of_pred _A p) (set_of_seq _A xq));;

end;; (*struct Predicate*)

module UnifyType : sig
  val b_of : SyntaxVCT.tau -> SyntaxVCT.bp
  val eq_i_i : 'a HOL.equal -> 'a -> 'a -> unit Predicate.pred
  val eq_o_i : 'a -> 'a Predicate.pred
  val fvs_t_bp : SyntaxVCT.bp -> string list
  val fvs_t_tau : SyntaxVCT.tau -> string list
  val fvs_t_ctor_tau : string * SyntaxVCT.tau -> string list
  val fvs_t_ctor_tau_list : (string * SyntaxVCT.tau) list -> string list
  val fvs_t_bp_list : SyntaxVCT.bp list -> string list
  val fvs_t_field_bp : string * SyntaxVCT.bp -> string list
  val fvs_t_field_bp_list : (string * SyntaxVCT.bp) list -> string list
  val tsubst_bp_list_list :
    SyntaxVCT.bp list -> (string * SyntaxVCT.bp) list -> SyntaxVCT.bp list
  val unify_b_i_i_o :
    SyntaxVCT.bp ->
      SyntaxVCT.bp -> (((string * SyntaxVCT.bp) list) option) Predicate.pred
  val unify_b_aux_list_i_i_o :
    SyntaxVCT.bp list ->
      SyntaxVCT.bp list ->
        (((string * SyntaxVCT.bp) list) option) Predicate.pred
  val unify_b_aux_i_i_o :
    SyntaxVCT.bp ->
      SyntaxVCT.bp -> (((string * SyntaxVCT.bp) list) option) Predicate.pred
end = struct

let rec b_of (SyntaxVCT.T_refined_type (uu, b, uv)) = b;;

let rec eq_i_i _A
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (x, xaa) ->
        (if HOL.eq _A x xaa then Predicate.single () else Predicate.bot_pred));;

let rec eq_o_i xa = Predicate.bind (Predicate.single xa) Predicate.single;;

let rec fvs_t_bp
  = function SyntaxVCT.B_var tvar -> [tvar]
    | SyntaxVCT.B_tid uu -> []
    | SyntaxVCT.B_int -> []
    | SyntaxVCT.B_bool -> []
    | SyntaxVCT.B_bit -> []
    | SyntaxVCT.B_unit -> []
    | SyntaxVCT.B_real -> []
    | SyntaxVCT.B_vec (order, bp) -> fvs_t_bp bp
    | SyntaxVCT.B_list bp -> fvs_t_bp bp
    | SyntaxVCT.B_tuple bp_list -> fvs_t_bp_list bp_list
    | SyntaxVCT.B_union (uv, ctor_tau_list) -> fvs_t_ctor_tau_list ctor_tau_list
    | SyntaxVCT.B_record field_bp_list -> fvs_t_field_bp_list field_bp_list
    | SyntaxVCT.B_undef -> []
    | SyntaxVCT.B_reg t -> fvs_t_tau t
    | SyntaxVCT.B_string -> []
    | SyntaxVCT.B_exception -> []
    | SyntaxVCT.B_finite_set num_list -> []
and fvs_t_tau (SyntaxVCT.T_refined_type (zp, bp, cp)) = fvs_t_bp bp
and fvs_t_ctor_tau (ctor_XXX, tau_XXX) = fvs_t_tau tau_XXX
and fvs_t_ctor_tau_list
  = function [] -> []
    | ctor_tau_XXX :: ctor_tau_list_XXX ->
        fvs_t_ctor_tau ctor_tau_XXX @ fvs_t_ctor_tau_list ctor_tau_list_XXX
and fvs_t_bp_list
  = function [] -> []
    | bp_XXX :: bp_list_XXX -> fvs_t_bp bp_XXX @ fvs_t_bp_list bp_list_XXX
and fvs_t_field_bp (field_XXX, bp_XXX) = fvs_t_bp bp_XXX
and fvs_t_field_bp_list
  = function [] -> []
    | field_bp_XXX :: field_bp_list_XXX ->
        fvs_t_field_bp field_bp_XXX @ fvs_t_field_bp_list field_bp_list_XXX;;

let rec tsubst_bp_list_list
  bp_list x1 = match bp_list, x1 with bp_list, [] -> bp_list
    | bp_list, (tvar, bp) :: bsub ->
        tsubst_bp_list_list (SyntaxPED.tsubst_bp_list bp tvar bp_list) bsub;;

let rec unify_b_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun (b1, b2) ->
          Predicate.bind
            (eq_i_i (Lista.equal_list Stringa.equal_literal) (fvs_t_bp b1) [])
            (fun () ->
              Predicate.bind
                (eq_i_i (Lista.equal_list Stringa.equal_literal) (fvs_t_bp b2)
                  [])
                (fun () ->
                  Predicate.bind (eq_i_i SyntaxVCT.equal_bp b1 b2)
                    (fun () -> Predicate.single (Some []))))))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun (b1, b2) ->
            Predicate.bind
              (eq_i_i (Lista.equal_list Stringa.equal_literal) (fvs_t_bp b1) [])
              (fun () ->
                Predicate.bind
                  (eq_i_i (Lista.equal_list Stringa.equal_literal) (fvs_t_bp b2)
                    [])
                  (fun () ->
                    Predicate.bind
                      (Predicate.if_pred (not (SyntaxVCT.equal_bpa b1 b2)))
                      (fun () -> Predicate.single None)))))
        (Predicate.bind (Predicate.single (x, xa))
          (fun (b1, b2) ->
            Predicate.bind
              (Predicate.if_pred
                (not (Lista.null (fvs_t_bp b1)) ||
                  not (Lista.null (fvs_t_bp b2))))
              (fun () ->
                Predicate.bind (unify_b_aux_i_i_o b1 b2) Predicate.single))))
and unify_b_aux_list_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], []) -> Predicate.single (Some [])
            | ([], _ :: _) -> Predicate.bot_pred
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (_ :: _, []) -> Predicate.bot_pred
            | (b1 :: bs1, b2 :: _) ->
              Predicate.bind (unify_b_i_i_o b1 b2)
                (fun aa ->
                  (match aa with None -> Predicate.bot_pred
                    | Some bsub1 ->
                      Predicate.bind
                        (unify_b_aux_list_i_i_o (tsubst_bp_list_list bs1 bsub1)
                          (tsubst_bp_list_list bs1 bsub1))
                        (fun ab ->
                          (match ab with None -> Predicate.bot_pred
                            | Some bsub2 ->
                              Predicate.single (Some (bsub1 @ bsub2)))))))))
and unify_b_aux_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (SyntaxVCT.B_var _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_var _) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_tid _) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_int) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_bool) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_bit) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_unit) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_real) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (ord, b1), SyntaxVCT.B_vec (orda, b2)) ->
              (if SyntaxVCT.equal_order ord orda
                then Predicate.bind (unify_b_i_i_o b1 b2) Predicate.single
                else Predicate.bot_pred)
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_list _) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_tuple _) ->
              Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_union (_, _)) ->
              Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_record _) ->
              Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_undef) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_reg _) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_string) -> Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_exception) ->
              Predicate.bot_pred
            | (SyntaxVCT.B_vec (_, _), SyntaxVCT.B_finite_set _) ->
              Predicate.bot_pred
            | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
            | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
            | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (SyntaxVCT.B_var _, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_var _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_tid _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_int) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_bool) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_bit) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_unit) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_real) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_vec (_, _)) ->
                Predicate.bot_pred
              | (SyntaxVCT.B_list b1, SyntaxVCT.B_list b2) ->
                Predicate.bind (unify_b_i_i_o b1 b2) Predicate.single
              | (SyntaxVCT.B_list _, SyntaxVCT.B_tuple _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_union (_, _)) ->
                Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_record _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_undef) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_reg _) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_string) -> Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_exception) ->
                Predicate.bot_pred
              | (SyntaxVCT.B_list _, SyntaxVCT.B_finite_set _) ->
                Predicate.bot_pred
              | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
              | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
              | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a
                with (SyntaxVCT.B_var bv, b) ->
                  Predicate.bind
                    (eq_i_i (Lista.equal_list Stringa.equal_literal)
                      (fvs_t_bp b) [])
                    (fun () -> Predicate.single (Some [(bv, b)]))
                | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
                | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
                | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
                | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a
                  with (b, SyntaxVCT.B_var bv) ->
                    Predicate.bind
                      (eq_i_i (Lista.equal_list Stringa.equal_literal)
                        (fvs_t_bp b) [])
                      (fun () -> Predicate.single (Some [(bv, b)]))
                  | (_, SyntaxVCT.B_tid _) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_int) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_bool) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_bit) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_unit) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_real) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_vec (_, _)) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_list _) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_tuple _) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_union (_, _)) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_record _) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_undef) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_reg _) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_string) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_exception) -> Predicate.bot_pred
                  | (_, SyntaxVCT.B_finite_set _) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a
                    with (SyntaxVCT.B_var bv, SyntaxVCT.B_var bva) ->
                      (if ((bv : string) = bva) then Predicate.single (Some [])
                        else Predicate.bot_pred)
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_tid _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_int) -> Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_bool) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_bit) -> Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_unit) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_real) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_vec (_, _)) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_list _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_tuple _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_union (_, _)) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_record _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_undef) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_reg _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_string) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_exception) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_var _, SyntaxVCT.B_finite_set _) ->
                      Predicate.bot_pred
                    | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
                    | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a with (SyntaxVCT.B_var _, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_var _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_tid _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_int) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_bool) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_bit) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_unit) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_real) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_vec (_, _)) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_list _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_tuple _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_union (_, _)) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record fs1, SyntaxVCT.B_record fs2) ->
                        Predicate.bind
                          (unify_b_aux_list_i_i_o
                            (Lista.map Product_Type.snd fs1)
                            (Lista.map Product_Type.snd fs2))
                          Predicate.single
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_undef) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_reg _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_string) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_exception) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_record _, SyntaxVCT.B_finite_set _) ->
                        Predicate.bot_pred
                      | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
                      | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a with (SyntaxVCT.B_var _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_var _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_tid _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_int) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_bool) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_bit) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_unit) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_real) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_vec (_, _)) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_list _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple bs1, SyntaxVCT.B_tuple bs2) ->
                          Predicate.bind (unify_b_aux_list_i_i_o bs1 bs2)
                            Predicate.single
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_union (_, _)) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_record _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_undef) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_reg _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_string) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_exception) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, SyntaxVCT.B_finite_set _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_finite_set _, _) -> Predicate.bot_pred)))
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a with (SyntaxVCT.B_var _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_tid _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_int, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_bool, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_bit, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_unit, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_real, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_vec (_, _), _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_list _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_tuple _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_var _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_tid _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_int) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_bool) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_bit) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_unit) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_real) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_vec (_, _)) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_list _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_tuple _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (s, fs1a),
                            SyntaxVCT.B_union (sa, fs2a))
                          -> (if ((s : string) = sa)
                               then Predicate.bind
                                      (unify_b_aux_list_i_i_o
(Lista.map (Fun.comp b_of Product_Type.snd) fs1a)
(Lista.map (Fun.comp b_of Product_Type.snd) fs2a))
                                      Predicate.single
                               else Predicate.bot_pred)
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_record _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_undef) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_reg _) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_string) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_exception) ->
                          Predicate.bot_pred
                        | (SyntaxVCT.B_union (_, _), SyntaxVCT.B_finite_set _)
                          -> Predicate.bot_pred
                        | (SyntaxVCT.B_record _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_undef, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_reg _, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_string, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_exception, _) -> Predicate.bot_pred
                        | (SyntaxVCT.B_finite_set _, _) ->
                          Predicate.bot_pred)))))))));;

end;; (*struct UnifyType*)

module TypingUtils : sig
  val k_list :
    (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list ->
      (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val g_cons3 :
    (SyntaxPED.pexpp, unit) Contexts.gamma_ext ->
      ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list) list ->
        (SyntaxPED.pexpp, unit) Contexts.gamma_ext
  val k_append :
    ((SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list) list ->
      (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val emptyEnv : (SyntaxPED.pexpp, unit) Contexts.gamma_ext
  val emptyTEnv : unit ContextsPiDelta.theta_ext
  val mk_constructor_fun :
    SyntaxVCT.tau ->
      SyntaxVCT.tau ->
        string ->
          ((SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list) option
  val lookup_fun :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        SyntaxVCT.xp ->
          ((SyntaxVCT.xp * (SyntaxVCT.ap * SyntaxPED.pexpp option)) list) option
  val fresh_string_aux : string list -> Arith.int list -> string
  val fresh_string : string list -> string
  val mk_fresh_g : (SyntaxPED.pexpp, unit) Contexts.gamma_ext -> SyntaxVCT.xp
  val mk_fresh_i : Arith.nat -> Arith.nat * SyntaxVCT.xp
  val add_fun_all :
    (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
      SyntaxVCT.ap ->
        SyntaxPED.funclp list -> (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext
  val mk_proj_var : SyntaxVCT.xp -> Arith.nat -> SyntaxVCT.xp
  val mk_eq_proj_aux :
    SyntaxVCT.xp -> Arith.nat -> Arith.nat -> SyntaxVCT.xp -> SyntaxVCT.cp
  val mk_proj_vars :
    SyntaxVCT.xp ->
      SyntaxVCT.bp list ->
        SyntaxVCT.xp list * (SyntaxVCT.xp * (SyntaxVCT.bp * SyntaxVCT.cp)) list
  val tsubst_t_many :
    SyntaxVCT.tau -> (string * SyntaxVCT.bp) list -> SyntaxVCT.tau
  val tsubst_bp_many :
    SyntaxVCT.bp -> (string * SyntaxVCT.bp) list -> SyntaxVCT.bp
  val lookup_fun_type :
    unit ContextsPiDelta.theta_ext ->
      (SyntaxPED.pexpp, unit) ContextsPiDelta.phi_ext ->
        SyntaxVCT.xp -> (SyntaxVCT.ap list) option
  val lookup_ctor_base :
    unit ContextsPiDelta.theta_ext ->
      string -> (SyntaxVCT.tau * SyntaxVCT.bp) option
end = struct

let rec k_list k = k;;

let rec g_cons3
  g klist =
    Contexts.add_vars g
      (Lista.map (fun (x, (b, c)) -> (x, Contexts.GEPair (b, c)))
        (Lista.concat klist));;

let rec k_append ks = Lista.concat ks;;

let emptyEnv : (SyntaxPED.pexpp, unit) Contexts.gamma_ext
  = Contexts.Gamma_ext
      (Finite_Map.fmempty, [], [], [], Finite_Map.fmempty, Finite_Map.fmempty,
        [], None, ());;

let emptyTEnv : unit ContextsPiDelta.theta_ext
  = ContextsPiDelta.Theta_ext
      ([], Finite_Map.fmempty, Some SyntaxVCT.Ord_inc, ());;

let rec mk_constructor_fun
  (SyntaxVCT.T_refined_type (z, b, c)) ret cn =
    (let x = "#x" in
      Some [(SyntaxVCT.VNamed cn,
              (SyntaxVCT.A_function
                 (SyntaxVCT.VNamed x, b,
                   SyntaxPED.subst_cp (SyntaxVCT.V_var (SyntaxVCT.VNamed x)) z
                     c,
                   SyntaxVCT.T_refined_type
                     (SyntaxVCT.VIndex, SyntaxUtils.b_of ret,
                       SyntaxVCT.C_eq
                         (SyntaxVCT.CE_val (SyntaxVCT.V_var SyntaxVCT.VIndex),
                           SyntaxVCT.CE_val
                             (SyntaxVCT.V_constr
                               (cn, SyntaxVCT.V_var (SyntaxVCT.VNamed x)))))),
                Some (SyntaxPED.PEXPp_exp
                       (SyntaxPED.Pp_id (Location.Loc_unknown, x),
                         SyntaxPED.Ep_val
                           (Location.Loc_unknown,
                             SyntaxVCT.V_constr
                               (cn, SyntaxVCT.V_var
                                      (SyntaxVCT.VNamed x)))))))]);;

let rec lookup_fun
  t gamma x2 = match t, gamma, x2 with
    t, gamma, SyntaxVCT.VNamed cn ->
      (match ContextsPiDelta.lookup_fun_aux gamma (SyntaxVCT.VNamed cn)
        with None ->
          (let _ = Debug.trace ("Did find function " ^ cn) in
            (match ContextsPiDelta.lookup_constr_union t cn with None -> None
              | Some ret ->
                (match ContextsPiDelta.lookup_constr_in_type ret cn
                  with None -> None | Some ta -> mk_constructor_fun ta ret cn)))
        | Some ta -> (let _ = Debug.trace ("found function " ^ cn) in Some ta))
    | uu, uv, SyntaxVCT.VIndex -> None;;

let rec fresh_string_aux
  ss x1 = match ss, x1 with ss, [] -> "_x_runout"
    | ss, n :: ns ->
        (let s = "_xx" ^ Utils.string_lit_of_int n in
          (if Lista.member Stringa.equal_literal ss s
            then fresh_string_aux ss ns else s));;

let rec fresh_string
  ss = fresh_string_aux ss
         (Lista.upto Arith.one_inta (Arith.Int_of_integer (Z.of_int 100)));;

let rec mk_fresh_g
  g = (let s =
         fresh_string
           (Lista.map (fun (x, _) -> Contexts.x_of x) (Contexts.gamma_x g))
         in
       let _ = Debug.trace ("mk_fresh: " ^ s) in
        SyntaxVCT.VNamed s);;

let rec mk_fresh_i
  i = (let s = "_x" ^ Stringa.implode (Utils.string_of_nat i) in
       let _ = Debug.trace ("mk_fresh: " ^ s) in
        (Arith.plus_nat i Arith.one_nat, SyntaxVCT.VNamed s));;

let rec add_fun_all
  g a x2 = match g, a, x2 with g, a, [] -> g
    | g, a, SyntaxPED.FCLp_funcl (uu, fid, pexp) :: fs ->
        add_fun_all
          (ContextsPiDelta.add_fun g (SyntaxVCT.VNamed fid, (a, Some pexp))) a
          fs;;

let rec mk_proj_var
  (SyntaxVCT.VNamed x) n =
    SyntaxVCT.VNamed ((x ^ "_") ^ Utils.string_lit_of_nat n);;

let rec mk_eq_proj_aux
  x i n xp =
    SyntaxVCT.C_eq
      (SyntaxVCT.CE_val (SyntaxVCT.V_var xp),
        SyntaxVCT.CE_val
          (SyntaxVCT.V_proj
            ((Utils.string_lit_of_nat n ^ "X") ^
               Utils.string_lit_of_nat (Arith.plus_nat i Arith.one_nat),
              SyntaxVCT.V_var x)));;

let rec mk_proj_vars
  x bs =
    (let ks =
       Contexts.mapi
         (fun i b ->
           (let xa = mk_proj_var x i in
             (xa, (b, mk_eq_proj_aux x (Arith.nat (Arith.int_of_nat i))
                        (Lista.size_list bs) xa))))
         bs
       in
      (Lista.map Product_Type.fst ks, ks));;

let rec tsubst_t_many
  b x1 = match b, x1 with b, [] -> b
    | ba, (bv, b) :: bsub -> SyntaxPED.tsubst_tp b bv (tsubst_t_many ba bsub);;

let rec tsubst_bp_many
  b x1 = match b, x1 with b, [] -> b
    | ba, (bv, b) :: bsub -> SyntaxPED.tsubst_bp b bv (tsubst_bp_many ba bsub);;

let rec lookup_fun_type
  t g x =
    (match lookup_fun t g x with None -> None
      | Some asa ->
        Some (Lista.map (fun (_, a) -> (let (aa, _) = a in aa)) asa));;

let rec lookup_ctor_base
  theta ctor =
    (match ContextsPiDelta.lookup_constr_union_type theta ctor with None -> None
      | Some (t1, t2) -> Some (t1, SyntaxUtils.b_of t2));;

end;; (*struct TypingUtils*)

module ConvertTypes : sig
  val elim :
    Arith.nat ->
      Z.t list * SyntaxVCT.cep ->
        Z.t list * SyntaxVCT.cep -> Z.t list * SyntaxVCT.cep
  val swap :
    Arith.nat ->
      Arith.nat ->
        (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val zipi : 'a list -> (Arith.nat * 'a) list
  val nonZeroElement :
    Arith.nat -> (Z.t list * SyntaxVCT.cep) list -> Arith.nat option
  val swap_if_0 :
    Arith.nat ->
      (Z.t list * SyntaxVCT.cep) list ->
        ((Z.t list * SyntaxVCT.cep) list) option
  val solve_jth :
    Arith.nat ->
      (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val solve : (Z.t list * SyntaxVCT.cep) list -> (Z.t list * SyntaxVCT.cep) list
  val is_const : Z.t list -> bool
  val extract_ce :
    Z.t -> Z.t -> SyntaxVCT.cep -> SyntaxVCT.cep * SyntaxVCT.cp list
  val solve_ce :
    (Z.t list * SyntaxVCT.cep) list -> SyntaxVCT.cep list * SyntaxVCT.cp list
  val coeff_mult_constant : Z.t -> (Z.t list) option -> (Z.t list) option
  val coeff_times : (Z.t list) option -> (Z.t list) option -> (Z.t list) option
  val coeff_plus : (Z.t list) option -> (Z.t list) option -> (Z.t list) option
  val linearise : SyntaxVCT.xp list -> SyntaxVCT.cep -> (Z.t list) option
  val linearise_A :
    SyntaxVCT.xp list ->
      (SyntaxVCT.cep * SyntaxVCT.cep) list ->
        ((Z.t list * SyntaxVCT.cep) list) option
  val solve_ce_ce :
    SyntaxVCT.xp list ->
      (SyntaxVCT.cep * SyntaxVCT.cep) list ->
        (SyntaxVCT.cep list * SyntaxVCT.cp list) option
end = struct

let rec elim
  j (cs1, ce1) (cs2, ce2) =
    (let cs1a =
       (if Z.equal (Lista.nth cs2 j) (Z.of_int 1) then cs1
         else Lista.map (fun x -> Z.mul x (Lista.nth cs2 j)) cs1)
       in
     let cs2a =
       (if Z.equal (Lista.nth cs1 j) (Z.of_int 1) then cs2
         else Lista.map (fun x -> Z.mul x (Lista.nth cs1 j)) cs2)
       in
     let ce1a =
       (if Z.equal (Lista.nth cs2 j) (Z.of_int 1) then ce1
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Times, ce1,
                  SyntaxVCT.CE_val
                    (SyntaxVCT.V_lit (SyntaxVCT.L_num (Lista.nth cs2 j)))))
       in
     let ce2a =
       (if Z.equal (Lista.nth cs1 j) (Z.of_int 1) then ce2
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Times, ce2,
                  SyntaxVCT.CE_val
                    (SyntaxVCT.V_lit (SyntaxVCT.L_num (Lista.nth cs1 j)))))
       in
     let cs2b = Lista.map (fun (a, b) -> Z.sub a b) (Lista.zip cs2a cs1a) in
     let a = SyntaxVCT.CE_bop (SyntaxVCT.Minus, ce2a, ce1a) in
      (cs2b, a));;

let rec swap
  i j a =
    (let b = Lista.nth a i in
      Lista.list_update (Lista.list_update a i (Lista.nth a j)) j b);;

let rec zipi xs = Lista.zip (Lista.upt Arith.zero_nat (Lista.size_list xs)) xs;;

let rec nonZeroElement
  j xs =
    (match
      Lista.filter
        (fun (i, (r, _)) ->
          Arith.less_eq_nat j i && not (Z.equal (Lista.nth r j) Z.zero))
        (zipi xs)
      with [] -> None | (x, _) :: _ -> Some x);;

let rec swap_if_0
  j a = (if Z.equal (Lista.nth (Product_Type.fst (Lista.nth a j)) j) Z.zero
          then (match nonZeroElement j a with None -> None
                 | Some i -> Some (swap i j a))
          else Some a);;

let rec solve_jth
  j a = (match swap_if_0 j a with None -> a
          | Some aa ->
            Lista.map
              (fun (i, (r, _)) ->
                (if Arith.equal_nat i j || Z.equal (Lista.nth r j) Z.zero
                  then Lista.nth aa i
                  else elim j (Lista.nth aa j) (Lista.nth aa i)))
              (zipi aa));;

let rec solve
  a = Lista.fold solve_jth
        (Lista.upt Arith.zero_nat
          (Arith.minus_nat
            (Lista.size_list (Product_Type.fst (Lista.nth a Arith.zero_nat)))
            Arith.one_nat))
        a;;

let rec is_const = function [x] -> true
                   | x :: v :: va -> Z.equal x Z.zero && is_const (v :: va);;

let rec extract_ce
  m n ce =
    (let cea =
       (if Z.equal m Z.zero then ce
         else SyntaxVCT.CE_bop
                (SyntaxVCT.Minus, ce,
                  SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num m))))
       in
      (if Z.equal n (Z.of_int 1) then (cea, [])
        else (SyntaxVCT.CE_bop
                (SyntaxVCT.Div, cea,
                  SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num n))),
               [SyntaxVCT.C_eq
                  (SyntaxVCT.CE_bop
                     (SyntaxVCT.Mod, cea,
                       SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num n))),
                    SyntaxVCT.CE_val
                      (SyntaxVCT.V_lit (SyntaxVCT.L_num Z.zero)))])));;

let rec solve_ce
  a = (let aa = solve a in
       let (xs, ys) =
         Utils.unzip
           (Lista.map
             (fun (i, (ces, ce)) ->
               (if Arith.less_eq_nat
                     (Arith.minus_nat (Lista.size_list ces) Arith.one_nat) i
                 then extract_ce
                        (Lista.nth ces
                          (Arith.minus_nat (Lista.size_list ces) Arith.one_nat))
                        (Z.of_int 1) ce
                 else extract_ce
                        (Lista.nth ces
                          (Arith.minus_nat (Lista.size_list ces) Arith.one_nat))
                        (Lista.nth ces i) ce))
             (zipi aa))
         in
        (xs, Lista.concat ys));;

let rec coeff_mult_constant
  i x1 = match i, x1 with i, Some xs -> Some (Lista.map (fun x -> Z.mul x i) xs)
    | i, None -> None;;

let rec coeff_times
  x0 uu = match x0, uu with
    Some xs, Some ys ->
      (if is_const xs then coeff_mult_constant (Lista.last xs) (Some ys)
        else (if is_const ys then coeff_mult_constant (Lista.last ys) (Some xs)
               else None))
    | None, uu -> None
    | Some v, None -> None;;

let rec coeff_plus
  x0 uu = match x0, uu with
    Some xs, Some ys ->
      Some (Lista.map (fun (a, b) -> Z.add a b) (Lista.zip xs ys))
    | None, uu -> None
    | Some v, None -> None;;

let rec linearise
  ks x1 = match ks, x1 with
    ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_num i)) ->
      Some (Lista.map (fun _ -> Z.zero) ks @ [i])
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_var x) ->
        Some (Lista.map
                (fun y ->
                  (if SyntaxVCT.equal_xpa x y then (Z.of_int 1) else Z.zero))
                ks @
               [Z.zero])
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Plus, ce1, ce2) ->
        coeff_plus (linearise ks ce1) (linearise ks ce2)
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Minus, ce1, ce2) ->
        coeff_plus (linearise ks ce1)
          (coeff_mult_constant (Z.neg (Z.of_int 1)) (linearise ks ce2))
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Times, ce1, ce2) ->
        coeff_times (linearise ks ce1) (linearise ks ce2)
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_unit) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_zero) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_one) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_true) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_false) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_bitvec vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_string vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit SyntaxVCT.L_undef) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_lit (SyntaxVCT.L_real vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_vec va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_list va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_cons (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_constr (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_record va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_tuple va) -> Some []
    | ks, SyntaxVCT.CE_val (SyntaxVCT.V_proj (va, vb)) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Div, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Mod, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.LEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.LT, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.GT, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.GEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Eq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.And, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.Or, va, vb) -> Some []
    | ks, SyntaxVCT.CE_bop (SyntaxVCT.NEq, va, vb) -> Some []
    | ks, SyntaxVCT.CE_many_plus v -> Some []
    | ks, SyntaxVCT.CE_uop (v, va) -> Some []
    | ks, SyntaxVCT.CE_proj (v, va) -> Some []
    | ks, SyntaxVCT.CE_field_access (v, va) -> Some [];;

let rec linearise_A
  ks x1 = match ks, x1 with ks, [] -> Some []
    | ks, (ce1, ce2) :: ces ->
        (match (linearise ks ce1, linearise_A ks ces) with (None, _) -> None
          | (Some _, None) -> None
          | (Some ce1a, Some cesa) -> Some ((ce1a, ce2) :: cesa));;

let rec solve_ce_ce
  ks ces =
    (match linearise_A ks ces with None -> None | Some a -> Some (solve_ce a));;

end;; (*struct ConvertTypes*)

