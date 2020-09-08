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
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit HOL.equal
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val equal_bool : bool -> bool -> bool
end = struct

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

let rec equal_unita u v = true;;

let equal_unit = ({HOL.equal = equal_unita} : unit HOL.equal);;

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

end;; (*struct Product_Type*)

module Option : sig
  val equal_optiona : 'a HOL.equal -> 'a option -> 'a option -> bool
  val equal_option : 'a HOL.equal -> ('a option) HOL.equal
  val bind : 'a option -> ('a -> 'b option) -> 'b option
  val map_option : ('a -> 'b) -> 'a option -> 'b option
end = struct

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> HOL.eq _A x2 y2
                           | None, None -> true;;

let rec equal_option _A =
  ({HOL.equal = equal_optiona _A} : ('a option) HOL.equal);;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

end;; (*struct Option*)

module Arith : sig
  type num = One | Bit0 of num | Bit1 of num
  type int = Zero_int | Pos of num | Neg of num
  val one_inta : int
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_int : int one
  val plus_num : num -> num -> num
  val uminus_int : int -> int
  val bitM : num -> num
  val dup : int -> int
  val plus_inta : int -> int -> int
  val sub : num -> num -> int
  val minus_int : int -> int -> int
  type 'a plus = {plus : 'a -> 'a -> 'a}
  val plus : 'a plus -> 'a -> 'a -> 'a
  val plus_int : int plus
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val zero_int : int zero
  type 'a semigroup_add = {plus_semigroup_add : 'a plus}
  type 'a numeral =
    {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add}
  val semigroup_add_int : int semigroup_add
  val numeral_int : int numeral
  val times_num : num -> num -> num
  val times_inta : int -> int -> int
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power = {one_power : 'a one; times_power : 'a times}
  val times_int : int times
  val power_int : int power
  type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add}
  type 'a semigroup_mult = {times_semigroup_mult : 'a times}
  type 'a semiring =
    {ab_semigroup_add_semiring : 'a ab_semigroup_add;
      semigroup_mult_semiring : 'a semigroup_mult}
  val ab_semigroup_add_int : int ab_semigroup_add
  val semigroup_mult_int : int semigroup_mult
  val semiring_int : int semiring
  type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero}
  val mult_zero_int : int mult_zero
  type 'a monoid_add =
    {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero}
  type 'a comm_monoid_add =
    {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
      monoid_add_comm_monoid_add : 'a monoid_add}
  type 'a semiring_0 =
    {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
      mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring}
  val monoid_add_int : int monoid_add
  val comm_monoid_add_int : int comm_monoid_add
  val semiring_0_int : int semiring_0
  type 'a monoid_mult =
    {semigroup_mult_monoid_mult : 'a semigroup_mult;
      power_monoid_mult : 'a power}
  type 'a semiring_numeral =
    {monoid_mult_semiring_numeral : 'a monoid_mult;
      numeral_semiring_numeral : 'a numeral;
      semiring_semiring_numeral : 'a semiring}
  type 'a zero_neq_one =
    {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero}
  type 'a semiring_1 =
    {semiring_numeral_semiring_1 : 'a semiring_numeral;
      semiring_0_semiring_1 : 'a semiring_0;
      zero_neq_one_semiring_1 : 'a zero_neq_one}
  val monoid_mult_int : int monoid_mult
  val semiring_numeral_int : int semiring_numeral
  val zero_neq_one_int : int zero_neq_one
  val semiring_1_int : int semiring_1
  val equal_integer : Z.t HOL.equal
  val one_integera : Z.t
  val one_integer : Z.t one
  val zero_integer : Z.t zero
  val zero_neq_one_integer : Z.t zero_neq_one
  type nat = Zero_nat | Suc of nat
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val nat_of_num : num -> nat
  val nat : int -> nat
  val of_bool : 'a zero_neq_one -> bool -> 'a
  val equal_num : num -> num -> bool
  val equal_int : int -> int -> bool
  val adjust_div : int * int -> int
  val adjust_mod : int -> int -> int
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val less_eq_nat : nat -> nat -> bool
  val divmod_nat : nat -> nat -> nat * nat
  val less_num : num -> num -> bool
  val less_eq_num : num -> num -> bool
  val less_int : int -> int -> bool
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val of_nat_aux : 'a semiring_1 -> ('a -> 'a) -> nat -> 'a -> 'a
  val of_nat : 'a semiring_1 -> nat -> 'a
  val bit_cut_integer : Z.t -> Z.t * bool
  val less_eq_int : int -> int -> bool
  val times_nat : nat -> nat -> nat
  val int_of_integer : Z.t -> int
  val divmod_step_int : num -> int * int -> int * int
  val divmod_int : num -> num -> int * int
  val modulo_int : int -> int -> int
  val divide_int : int -> int -> int
  val integer_of_int : int -> Z.t
  val divide_nat : nat -> nat -> nat
  val modulo_nat : nat -> nat -> nat
end = struct

type num = One | Bit0 of num | Bit1 of num;;

type int = Zero_int | Pos of num | Neg of num;;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec uminus_int = function Neg m -> Pos m
                     | Pos m -> Neg m
                     | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec plus_inta k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
                    | Neg m, Pos n -> sub n m
                    | Pos m, Neg n -> sub m n
                    | Pos m, Pos n -> Pos (plus_num m n)
                    | Zero_int, l -> l
                    | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_int l
                | k, Zero_int -> k;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_int = ({plus = plus_inta} : int plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = Zero_int} : int zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_inta k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                     | Neg m, Pos n -> Neg (times_num m n)
                     | Pos m, Neg n -> Neg (times_num m n)
                     | Pos m, Pos n -> Pos (times_num m n)
                     | Zero_int, l -> Zero_int
                     | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_int = ({times = times_inta} : int times);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let equal_integer = ({HOL.equal = Z.equal} : Z.t HOL.equal);;

let one_integera : Z.t = (Z.of_int 1);;

let one_integer = ({one = one_integera} : Z.t one);;

let zero_integer = ({zero = Z.zero} : Z.t zero);;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Z.t zero_neq_one);;

type nat = Zero_nat | Suc of nat;;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nat m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nat m m)
    | One -> one_nat;;

let rec nat = function Pos k -> nat_of_num k
              | Zero_int -> Zero_nat
              | Neg k -> Zero_nat;;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

let rec equal_int x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                    | Neg k, Pos l -> false
                    | Neg k, Zero_int -> false
                    | Pos k, Neg l -> false
                    | Pos k, Pos l -> equal_num k l
                    | Pos k, Zero_int -> false
                    | Zero_int, Neg l -> false
                    | Zero_int, Pos l -> false
                    | Zero_int, Zero_int -> true;;

let rec adjust_div
  (q, r) = plus_inta q (of_bool zero_neq_one_int (not (equal_int r Zero_int)));;

let rec adjust_mod
  l r = (if equal_int r Zero_int then Zero_int else minus_int l r);;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec equal_nat x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                    | Suc x2, Zero_nat -> false
                    | Suc x2, Suc y2 -> equal_nat x2 y2
                    | Zero_nat, Zero_nat -> true;;

let rec less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
                   | n, Zero_nat -> false
and less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                  | Zero_nat, n -> true;;

let rec divmod_nat
  m n = (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let a = divmod_nat (minus_nat m n) n in
                let (q, aa) = a in
                 (Suc q, aa)));;

let rec less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
                   | Bit1 m, Bit1 n -> less_num m n
                   | Bit0 m, Bit1 n -> less_eq_num m n
                   | Bit0 m, Bit0 n -> less_num m n
                   | One, Bit1 n -> true
                   | One, Bit0 n -> true
                   | m, One -> false
and less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                  | Bit1 m, Bit1 n -> less_eq_num m n
                  | Bit0 m, Bit1 n -> less_eq_num m n
                  | Bit0 m, Bit0 n -> less_eq_num m n
                  | Bit1 m, One -> false
                  | Bit0 m, One -> false
                  | One, n -> true;;

let rec less_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
                   | Neg k, Pos l -> true
                   | Neg k, Zero_int -> true
                   | Pos k, Neg l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Neg l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

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

let rec of_nat_aux _A inc x1 i = match inc, x1, i with inc, Zero_nat, i -> i
                        | inc, Suc n, i -> of_nat_aux _A inc n (inc i);;

let rec of_nat _A
  n = of_nat_aux _A
        (fun i ->
          plus _A.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
            i (one _A.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
        n (zero _A.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec bit_cut_integer
  k = (if Z.equal k Z.zero then (Z.zero, false)
        else (let (r, s) =
                (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                  k (Z.of_int 2)
                in
               ((if Z.lt Z.zero k then r else Z.sub (Z.neg r) s),
                 Z.equal s (Z.of_int 1))));;

let rec less_eq_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_eq_num l k
                      | Neg k, Pos l -> true
                      | Neg k, Zero_int -> true
                      | Pos k, Neg l -> false
                      | Pos k, Pos l -> less_eq_num k l
                      | Pos k, Zero_int -> false
                      | Zero_int, Neg l -> false
                      | Zero_int, Pos l -> true
                      | Zero_int, Zero_int -> true;;

let rec times_nat x0 n = match x0, n with Zero_nat, n -> Zero_nat
                    | Suc m, n -> plus_nat n (times_nat m n);;

let rec int_of_integer
  k = (if Z.lt k Z.zero then uminus_int (int_of_integer (Z.neg k))
        else (if Z.equal k Z.zero then Zero_int
               else (let (l, j) = divmod_integer k (Z.of_int 2) in
                     let la = times_inta (Pos (Bit0 One)) (int_of_integer l) in
                      (if Z.equal j Z.zero then la
                        else plus_inta la one_inta))));;

let rec divmod_step_int
  l (q, r) =
    (if less_eq_int (Pos l) r
      then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
             minus_int r (Pos l))
      else (times_inta (Pos (Bit0 One)) q, r));;

let rec divmod_int
  x0 x1 = match x0, x1 with
    Bit1 m, Bit1 n ->
      (if less_num m n then (Zero_int, Pos (Bit1 m))
        else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_inta (Pos (Bit0 One)) r))
    | One, Bit1 n -> (Zero_int, Pos One)
    | One, Bit0 n -> (Zero_int, Pos One)
    | Bit1 m, One -> (Pos (Bit1 m), Zero_int)
    | Bit0 m, One -> (Pos (Bit0 m), Zero_int)
    | One, One -> (Pos One, Zero_int);;

let rec modulo_int
  k ka = match k, ka with
    Neg m, Neg n -> uminus_int (Product_Type.snd (divmod_int m n))
    | Pos m, Neg n ->
        uminus_int (adjust_mod (Pos n) (Product_Type.snd (divmod_int m n)))
    | Neg m, Pos n -> adjust_mod (Pos n) (Product_Type.snd (divmod_int m n))
    | Pos m, Pos n -> Product_Type.snd (divmod_int m n)
    | k, Neg One -> Zero_int
    | k, Pos One -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Zero_int -> k;;

let rec divide_int
  k ka = match k, ka with Neg m, Neg n -> Product_Type.fst (divmod_int m n)
    | Pos m, Neg n -> uminus_int (adjust_div (divmod_int m n))
    | Neg m, Pos n -> uminus_int (adjust_div (divmod_int m n))
    | Pos m, Pos n -> Product_Type.fst (divmod_int m n)
    | k, Neg One -> uminus_int k
    | k, Pos One -> k
    | Zero_int, k -> Zero_int
    | k, Zero_int -> Zero_int;;

let rec integer_of_int
  k = (if less_int k Zero_int then Z.neg (integer_of_int (uminus_int k))
        else (if equal_int k Zero_int then Z.zero
               else (let l =
                       Z.mul (Z.of_int 2)
                         (integer_of_int (divide_int k (Pos (Bit0 One))))
                       in
                     let j = modulo_int k (Pos (Bit0 One)) in
                      (if equal_int j Zero_int then l
                        else Z.add l (Z.of_int 1)))));;

let rec divide_nat m n = Product_Type.fst (divmod_nat m n);;

let rec modulo_nat m n = Product_Type.snd (divmod_nat m n);;

end;; (*struct Arith*)

module Lista : sig
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val find : ('a -> bool) -> 'a list -> 'a option
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val null : 'a list -> bool
  val those : ('a option) list -> ('a list) option
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val hd : 'a list -> 'a
  val map : ('a -> 'b) -> 'a list -> 'b list
  val removeAll : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val replicate : Arith.nat -> 'a -> 'a list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val size_list : 'a list -> Arith.nat
end = struct

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({HOL.equal = equal_lista _A} : ('a list) HOL.equal);;

let rec upt
  i j = (if Arith.less_nat i j then i :: upt (Arith.Suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec find uu x1 = match uu, x1 with uu, [] -> None
               | p, x :: xs -> (if p x then Some x else find p xs);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> Option.map_option (fun a -> y :: a) (those xs));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> HOL.eq _A x y || member _A xs y;;

let rec insert _A x xs = (if member _A xs x then xs else x :: xs);;

let rec hd (x21 :: x22) = x21;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if HOL.eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec replicate xa0 x = match xa0, x with Arith.Zero_nat, x -> []
                    | Arith.Suc n, x -> x :: replicate n x;;

let rec gen_length
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.Suc n) xs
    | n, [] -> n;;

let rec size_list x = gen_length Arith.Zero_nat x;;

end;; (*struct Lista*)

module SailAST : sig
  type id = Id of string | Operator of string
  val equal_ida : id -> id -> bool
  val equal_id : id HOL.equal
  type kid = Var of string
  type order = Ord_var of kid | Ord_inc | Ord_dec
  type nexp = Nexp_id of id | Nexp_var of kid | Nexp_constant of Z.t |
    Nexp_app of id * nexp list | Nexp_times of nexp * nexp |
    Nexp_sum of nexp * nexp | Nexp_minus of nexp * nexp | Nexp_exp of nexp |
    Nexp_neg of nexp
  type kind = K_type | K_int | K_order | K_bool
  type kinded_id = KOpt_kind of kind * kid
  type base_effect = BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem
    | BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_undef | BE_unspec |
    BE_nondet | BE_escape | BE_config
  type effect = Effect_set of base_effect list
  type n_constraint = NC_equal of nexp * nexp | NC_bounded_ge of nexp * nexp |
    NC_bounded_gt of nexp * nexp | NC_bounded_le of nexp * nexp |
    NC_bounded_lt of nexp * nexp | NC_not_equal of nexp * nexp |
    NC_set of kid * Z.t list | NC_or of n_constraint * n_constraint |
    NC_and of n_constraint * n_constraint | NC_app of id * typ_arg list |
    NC_var of kid | NC_true | NC_false
  and typ_arg = A_nexp of nexp | A_typ of typ | A_order of order |
    A_bool of n_constraint
  and typ = Typ_internal_unknown | Typ_id of id | Typ_var of kid |
    Typ_fn of typ list * typ * effect | Typ_bidir of typ * typ * effect |
    Typ_tup of typ list | Typ_app of id * typ_arg list |
    Typ_exist of kinded_id list * n_constraint * typ
  val equal_kid : kid -> kid -> bool
  val equal_nexpa : nexp -> nexp -> bool
  val equal_nexp : nexp HOL.equal
  val equal_order : order -> order -> bool
  val equal_base_effecta : base_effect -> base_effect -> bool
  val equal_base_effect : base_effect HOL.equal
  val equal_effect : effect -> effect -> bool
  val equal_kind : kind -> kind -> bool
  val equal_kinded_ida : kinded_id -> kinded_id -> bool
  val equal_kinded_id : kinded_id HOL.equal
  val equal_typ : typ HOL.equal
  val equal_typa : typ -> typ -> bool
  val equal_typ_arga : typ_arg -> typ_arg -> bool
  val equal_typ_arg : typ_arg HOL.equal
  val equal_n_constraint : n_constraint -> n_constraint -> bool
  type type_union = Tu_ty_id of typ * id
  type quant_item = QI_id of kinded_id | QI_constraint of n_constraint |
    QI_constant of kinded_id list
  type typquant = TypQ_tq of quant_item list | TypQ_no_forall
  type tannot_opt = Typ_annot_opt_none | Typ_annot_opt_some of typquant * typ
  type effect_opt = Effect_opt_none | Effect_opt_effect of effect
  type typ_pat = TP_wild | TP_var of kid | TP_app of id * typ_pat list
  type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
    L_hex of string | L_bin of string | L_string of string | L_undef |
    L_real of string
  type 'a pat = P_lit of 'a * lit | P_wild of 'a | P_or of 'a * 'a pat * 'a pat
    | P_not of 'a * 'a pat | P_as of 'a * 'a pat * id |
    P_typ of 'a * typ * 'a pat | P_id of 'a * id |
    P_var of 'a * 'a pat * typ_pat | P_app of 'a * id * 'a pat list |
    P_vector of 'a * 'a pat list | P_vector_concat of 'a * 'a pat list |
    P_tup of 'a * 'a pat list | P_list of 'a * 'a pat list |
    P_cons of 'a * 'a pat * 'a pat | P_string_append of 'a * 'a pat list
  type value = Val
  type loop = While | Until
  type 'a exp = E_block of 'a * 'a exp list | E_id of 'a * id |
    E_lit of 'a * lit | E_cast of 'a * typ * 'a exp |
    E_app of 'a * id * 'a exp list | E_app_infix of 'a * 'a exp * id * 'a exp |
    E_tuple of 'a * 'a exp list | E_if of 'a * 'a exp * 'a exp * 'a exp |
    E_loop of 'a * loop * 'a internal_loop_measure * 'a exp * 'a exp |
    E_for of 'a * id * 'a exp * 'a exp * 'a exp * order * 'a exp |
    E_vector of 'a * 'a exp list | E_vector_access of 'a * 'a exp * 'a exp |
    E_vector_subrange of 'a * 'a exp * 'a exp * 'a exp |
    E_vector_update of 'a * 'a exp * 'a exp * 'a exp |
    E_vector_update_subrange of 'a * 'a exp * 'a exp * 'a exp * 'a exp |
    E_vector_append of 'a * 'a exp * 'a exp | E_list of 'a * 'a exp list |
    E_cons of 'a * 'a exp * 'a exp | E_record of 'a * 'a fexp list |
    E_record_update of 'a * 'a exp * 'a fexp list | E_field of 'a * 'a exp * id
    | E_case of 'a * 'a exp * 'a pexp list | E_let of 'a * 'a letbind * 'a exp |
    E_assign of 'a * 'a lexp * 'a exp | E_sizeof of 'a * nexp |
    E_return of 'a * 'a exp | E_exit of 'a * 'a exp | E_ref of 'a * id |
    E_throw of 'a * 'a exp | E_try of 'a * 'a exp * 'a pexp list |
    E_assert of 'a * 'a exp * 'a exp | E_var of 'a * 'a lexp * 'a exp * 'a exp |
    E_internal_plet of 'a * 'a pat * 'a exp * 'a exp |
    E_internal_return of 'a * 'a exp | E_internal_value of 'a * value |
    E_constraint of 'a * n_constraint
  and 'a fexp = FE_Fexp of 'a * id * 'a exp
  and 'a lexp = LEXP_id of 'a * id | LEXP_deref of 'a * 'a exp |
    LEXP_memory of 'a * id * 'a exp list | LEXP_cast of 'a * typ * id |
    LEXP_tup of 'a * 'a lexp list | LEXP_vector_concat of 'a * 'a lexp list |
    LEXP_vector of 'a * 'a lexp * 'a exp |
    LEXP_vector_range of 'a * 'a lexp * 'a exp * 'a exp |
    LEXP_field of 'a * 'a lexp * id
  and 'a pexp = Pat_exp of 'a * 'a pat * 'a exp |
    Pat_when of 'a * 'a pat * 'a exp * 'a exp
  and 'a letbind = LB_val of 'a * 'a pat * 'a exp
  and 'a internal_loop_measure = Measure_none | Measure_some of 'a exp
  type 'a rec_opt = Rec_nonrec | Rec_rec | Rec_measure of 'a pat * 'a exp
  type 'a mpat = MP_lit of 'a * lit | MP_id of 'a * id |
    MP_app of 'a * id * 'a mpat list | MP_vector of 'a * 'a mpat list |
    MP_vector_concat of 'a * 'a mpat list | MP_tup of 'a * 'a mpat list |
    MP_list of 'a * 'a mpat list | MP_cons of 'a * 'a mpat * 'a mpat |
    MP_string_append of 'a * 'a mpat list | MP_typ of 'a * 'a mpat * typ |
    MP_as of 'a * 'a mpat * id
  type 'a mpexp = MPat_pat of 'a * 'a mpat | MPat_when of 'a * 'a mpat * 'a exp
  type 'a mapcl = MCL_bidir of 'a * 'a mpexp * 'a mpexp |
    MCL_forwards of 'a * 'a mpexp * 'a exp |
    MCL_backwards of 'a * 'a mpexp * 'a exp
  type 'a pexp_funcl = PEXP_funcl of 'a pexp
  type 'a funcl = FCL_Funcl of 'a * id * 'a pexp_funcl
  type 'a scattered_def =
    SD_function of 'a * 'a rec_opt * tannot_opt * effect_opt * id |
    SD_funcl of 'a * 'a funcl | SD_variant of 'a * id * typquant |
    SD_unioncl of 'a * id * type_union | SD_mapping of 'a * id * tannot_opt |
    SD_mapcl of 'a * id * 'a mapcl | SD_end of 'a * id
  type 'a loop_measure = Loop of loop * 'a exp
  type default_spec = DT_order of order
  type typschm = TypSchm_ts of typquant * typ
  type val_spec =
    VS_aux of (typschm * (id * ((string -> string option) * bool)))
  type index_range = BF_single of nexp | BF_range of nexp * nexp |
    BF_concat of index_range * index_range
  type type_def_aux = TD_abbrev of id * typquant * typ_arg |
    TD_record of id * typquant * (typ * id) list * bool |
    TD_variant of id * typquant * type_union list * bool |
    TD_enum of id * id list * bool |
    TD_bitfield of id * typ * (id * index_range) list
  type type_def = TD_aux of type_def_aux
  type 'a reg_id = RI_id of 'a * id
  type 'a alias_spec = AL_subreg of 'a * 'a reg_id * id |
    AL_bit of 'a * 'a reg_id * 'a exp |
    AL_slice of 'a * 'a reg_id * 'a exp * 'a exp |
    AL_concat of 'a * 'a reg_id * 'a reg_id
  type 'a dec_spec = DEC_reg of 'a * effect * effect * typ * id |
    DEC_config of 'a * id * typ * 'a exp | DEC_alias of 'a * id * 'a alias_spec
    | DEC_typ_alias of 'a * typ * id * 'a alias_spec
  type 'a mapdef = MD_mapping of 'a * id * tannot_opt * 'a mapcl list
  type 'a fundef =
    FD_function of 'a * 'a rec_opt * tannot_opt * effect_opt * 'a funcl list
  type prec = Infix | InfixL | InfixR
  type 'a def = DEF_type of type_def | DEF_fundef of 'a fundef |
    DEF_mapdef of 'a mapdef | DEF_val of 'a letbind | DEF_spec of val_spec |
    DEF_fixity of prec * Z.t * id | DEF_overload of id * id list |
    DEF_default of default_spec | DEF_scattered of 'a scattered_def |
    DEF_measure of id * 'a pat * 'a exp |
    DEF_loop_measures of id * 'a loop_measure list | DEF_reg_dec of 'a dec_spec
    | DEF_internal_mutrec of 'a fundef list | DEF_pragma of string * string
  val annot_e : 'a exp -> 'a
  val annot_pat : 'a pat -> 'a
  val annot_lexp : 'a lexp -> 'a
end = struct

type id = Id of string | Operator of string;;

let rec equal_ida x0 x1 = match x0, x1 with Id x1, Operator x2 -> false
                    | Operator x2, Id x1 -> false
                    | Operator x2, Operator y2 -> ((x2 : string) = y2)
                    | Id x1, Id y1 -> ((x1 : string) = y1);;

let equal_id = ({HOL.equal = equal_ida} : id HOL.equal);;

type kid = Var of string;;

type order = Ord_var of kid | Ord_inc | Ord_dec;;

type nexp = Nexp_id of id | Nexp_var of kid | Nexp_constant of Z.t |
  Nexp_app of id * nexp list | Nexp_times of nexp * nexp |
  Nexp_sum of nexp * nexp | Nexp_minus of nexp * nexp | Nexp_exp of nexp |
  Nexp_neg of nexp;;

type kind = K_type | K_int | K_order | K_bool;;

type kinded_id = KOpt_kind of kind * kid;;

type base_effect = BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem |
  BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_undef | BE_unspec |
  BE_nondet | BE_escape | BE_config;;

type effect = Effect_set of base_effect list;;

type n_constraint = NC_equal of nexp * nexp | NC_bounded_ge of nexp * nexp |
  NC_bounded_gt of nexp * nexp | NC_bounded_le of nexp * nexp |
  NC_bounded_lt of nexp * nexp | NC_not_equal of nexp * nexp |
  NC_set of kid * Z.t list | NC_or of n_constraint * n_constraint |
  NC_and of n_constraint * n_constraint | NC_app of id * typ_arg list |
  NC_var of kid | NC_true | NC_false
and typ_arg = A_nexp of nexp | A_typ of typ | A_order of order |
  A_bool of n_constraint
and typ = Typ_internal_unknown | Typ_id of id | Typ_var of kid |
  Typ_fn of typ list * typ * effect | Typ_bidir of typ * typ * effect |
  Typ_tup of typ list | Typ_app of id * typ_arg list |
  Typ_exist of kinded_id list * n_constraint * typ;;

let rec equal_kid (Var x) (Var ya) = ((x : string) = ya);;

let rec equal_nexpa
  x0 x1 = match x0, x1 with Nexp_exp x8, Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_exp x8 -> false
    | Nexp_minus (x71, x72), Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_minus (x71, x72) -> false
    | Nexp_sum (x61, x62), Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_sum (x61, x62) -> false
    | Nexp_times (x51, x52), Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_times (x51, x52) -> false
    | Nexp_app (x41, x42), Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_app (x41, x42) -> false
    | Nexp_constant x3, Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_constant x3 -> false
    | Nexp_var x2, Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_var x2 -> false
    | Nexp_var x2, Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_var x2 -> false
    | Nexp_var x2, Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_var x2 -> false
    | Nexp_var x2, Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_var x2 -> false
    | Nexp_var x2, Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_var x2 -> false
    | Nexp_var x2, Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_var x2 -> false
    | Nexp_var x2, Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_var x2 -> false
    | Nexp_id x1, Nexp_neg x9 -> false
    | Nexp_neg x9, Nexp_id x1 -> false
    | Nexp_id x1, Nexp_exp x8 -> false
    | Nexp_exp x8, Nexp_id x1 -> false
    | Nexp_id x1, Nexp_minus (x71, x72) -> false
    | Nexp_minus (x71, x72), Nexp_id x1 -> false
    | Nexp_id x1, Nexp_sum (x61, x62) -> false
    | Nexp_sum (x61, x62), Nexp_id x1 -> false
    | Nexp_id x1, Nexp_times (x51, x52) -> false
    | Nexp_times (x51, x52), Nexp_id x1 -> false
    | Nexp_id x1, Nexp_app (x41, x42) -> false
    | Nexp_app (x41, x42), Nexp_id x1 -> false
    | Nexp_id x1, Nexp_constant x3 -> false
    | Nexp_constant x3, Nexp_id x1 -> false
    | Nexp_id x1, Nexp_var x2 -> false
    | Nexp_var x2, Nexp_id x1 -> false
    | Nexp_neg x9, Nexp_neg y9 -> equal_nexpa x9 y9
    | Nexp_exp x8, Nexp_exp y8 -> equal_nexpa x8 y8
    | Nexp_minus (x71, x72), Nexp_minus (y71, y72) ->
        equal_nexpa x71 y71 && equal_nexpa x72 y72
    | Nexp_sum (x61, x62), Nexp_sum (y61, y62) ->
        equal_nexpa x61 y61 && equal_nexpa x62 y62
    | Nexp_times (x51, x52), Nexp_times (y51, y52) ->
        equal_nexpa x51 y51 && equal_nexpa x52 y52
    | Nexp_app (x41, x42), Nexp_app (y41, y42) ->
        equal_ida x41 y41 && Lista.equal_lista (equal_nexp ()) x42 y42
    | Nexp_constant x3, Nexp_constant y3 -> Z.equal x3 y3
    | Nexp_var x2, Nexp_var y2 -> equal_kid x2 y2
    | Nexp_id x1, Nexp_id y1 -> equal_ida x1 y1
and equal_nexp () = ({HOL.equal = equal_nexpa} : nexp HOL.equal);;
let equal_nexp = equal_nexp ();;

let rec equal_order x0 x1 = match x0, x1 with Ord_inc, Ord_dec -> false
                      | Ord_dec, Ord_inc -> false
                      | Ord_var x1, Ord_dec -> false
                      | Ord_dec, Ord_var x1 -> false
                      | Ord_var x1, Ord_inc -> false
                      | Ord_inc, Ord_var x1 -> false
                      | Ord_var x1, Ord_var y1 -> equal_kid x1 y1
                      | Ord_dec, Ord_dec -> true
                      | Ord_inc, Ord_inc -> true;;

let rec equal_base_effecta
  x0 x1 = match x0, x1 with BE_escape, BE_config -> false
    | BE_config, BE_escape -> false
    | BE_nondet, BE_config -> false
    | BE_config, BE_nondet -> false
    | BE_nondet, BE_escape -> false
    | BE_escape, BE_nondet -> false
    | BE_unspec, BE_config -> false
    | BE_config, BE_unspec -> false
    | BE_unspec, BE_escape -> false
    | BE_escape, BE_unspec -> false
    | BE_unspec, BE_nondet -> false
    | BE_nondet, BE_unspec -> false
    | BE_undef, BE_config -> false
    | BE_config, BE_undef -> false
    | BE_undef, BE_escape -> false
    | BE_escape, BE_undef -> false
    | BE_undef, BE_nondet -> false
    | BE_nondet, BE_undef -> false
    | BE_undef, BE_unspec -> false
    | BE_unspec, BE_undef -> false
    | BE_depend, BE_config -> false
    | BE_config, BE_depend -> false
    | BE_depend, BE_escape -> false
    | BE_escape, BE_depend -> false
    | BE_depend, BE_nondet -> false
    | BE_nondet, BE_depend -> false
    | BE_depend, BE_unspec -> false
    | BE_unspec, BE_depend -> false
    | BE_depend, BE_undef -> false
    | BE_undef, BE_depend -> false
    | BE_barr, BE_config -> false
    | BE_config, BE_barr -> false
    | BE_barr, BE_escape -> false
    | BE_escape, BE_barr -> false
    | BE_barr, BE_nondet -> false
    | BE_nondet, BE_barr -> false
    | BE_barr, BE_unspec -> false
    | BE_unspec, BE_barr -> false
    | BE_barr, BE_undef -> false
    | BE_undef, BE_barr -> false
    | BE_barr, BE_depend -> false
    | BE_depend, BE_barr -> false
    | BE_wmvt, BE_config -> false
    | BE_config, BE_wmvt -> false
    | BE_wmvt, BE_escape -> false
    | BE_escape, BE_wmvt -> false
    | BE_wmvt, BE_nondet -> false
    | BE_nondet, BE_wmvt -> false
    | BE_wmvt, BE_unspec -> false
    | BE_unspec, BE_wmvt -> false
    | BE_wmvt, BE_undef -> false
    | BE_undef, BE_wmvt -> false
    | BE_wmvt, BE_depend -> false
    | BE_depend, BE_wmvt -> false
    | BE_wmvt, BE_barr -> false
    | BE_barr, BE_wmvt -> false
    | BE_wmv, BE_config -> false
    | BE_config, BE_wmv -> false
    | BE_wmv, BE_escape -> false
    | BE_escape, BE_wmv -> false
    | BE_wmv, BE_nondet -> false
    | BE_nondet, BE_wmv -> false
    | BE_wmv, BE_unspec -> false
    | BE_unspec, BE_wmv -> false
    | BE_wmv, BE_undef -> false
    | BE_undef, BE_wmv -> false
    | BE_wmv, BE_depend -> false
    | BE_depend, BE_wmv -> false
    | BE_wmv, BE_barr -> false
    | BE_barr, BE_wmv -> false
    | BE_wmv, BE_wmvt -> false
    | BE_wmvt, BE_wmv -> false
    | BE_exmem, BE_config -> false
    | BE_config, BE_exmem -> false
    | BE_exmem, BE_escape -> false
    | BE_escape, BE_exmem -> false
    | BE_exmem, BE_nondet -> false
    | BE_nondet, BE_exmem -> false
    | BE_exmem, BE_unspec -> false
    | BE_unspec, BE_exmem -> false
    | BE_exmem, BE_undef -> false
    | BE_undef, BE_exmem -> false
    | BE_exmem, BE_depend -> false
    | BE_depend, BE_exmem -> false
    | BE_exmem, BE_barr -> false
    | BE_barr, BE_exmem -> false
    | BE_exmem, BE_wmvt -> false
    | BE_wmvt, BE_exmem -> false
    | BE_exmem, BE_wmv -> false
    | BE_wmv, BE_exmem -> false
    | BE_eamem, BE_config -> false
    | BE_config, BE_eamem -> false
    | BE_eamem, BE_escape -> false
    | BE_escape, BE_eamem -> false
    | BE_eamem, BE_nondet -> false
    | BE_nondet, BE_eamem -> false
    | BE_eamem, BE_unspec -> false
    | BE_unspec, BE_eamem -> false
    | BE_eamem, BE_undef -> false
    | BE_undef, BE_eamem -> false
    | BE_eamem, BE_depend -> false
    | BE_depend, BE_eamem -> false
    | BE_eamem, BE_barr -> false
    | BE_barr, BE_eamem -> false
    | BE_eamem, BE_wmvt -> false
    | BE_wmvt, BE_eamem -> false
    | BE_eamem, BE_wmv -> false
    | BE_wmv, BE_eamem -> false
    | BE_eamem, BE_exmem -> false
    | BE_exmem, BE_eamem -> false
    | BE_wmem, BE_config -> false
    | BE_config, BE_wmem -> false
    | BE_wmem, BE_escape -> false
    | BE_escape, BE_wmem -> false
    | BE_wmem, BE_nondet -> false
    | BE_nondet, BE_wmem -> false
    | BE_wmem, BE_unspec -> false
    | BE_unspec, BE_wmem -> false
    | BE_wmem, BE_undef -> false
    | BE_undef, BE_wmem -> false
    | BE_wmem, BE_depend -> false
    | BE_depend, BE_wmem -> false
    | BE_wmem, BE_barr -> false
    | BE_barr, BE_wmem -> false
    | BE_wmem, BE_wmvt -> false
    | BE_wmvt, BE_wmem -> false
    | BE_wmem, BE_wmv -> false
    | BE_wmv, BE_wmem -> false
    | BE_wmem, BE_exmem -> false
    | BE_exmem, BE_wmem -> false
    | BE_wmem, BE_eamem -> false
    | BE_eamem, BE_wmem -> false
    | BE_rmemt, BE_config -> false
    | BE_config, BE_rmemt -> false
    | BE_rmemt, BE_escape -> false
    | BE_escape, BE_rmemt -> false
    | BE_rmemt, BE_nondet -> false
    | BE_nondet, BE_rmemt -> false
    | BE_rmemt, BE_unspec -> false
    | BE_unspec, BE_rmemt -> false
    | BE_rmemt, BE_undef -> false
    | BE_undef, BE_rmemt -> false
    | BE_rmemt, BE_depend -> false
    | BE_depend, BE_rmemt -> false
    | BE_rmemt, BE_barr -> false
    | BE_barr, BE_rmemt -> false
    | BE_rmemt, BE_wmvt -> false
    | BE_wmvt, BE_rmemt -> false
    | BE_rmemt, BE_wmv -> false
    | BE_wmv, BE_rmemt -> false
    | BE_rmemt, BE_exmem -> false
    | BE_exmem, BE_rmemt -> false
    | BE_rmemt, BE_eamem -> false
    | BE_eamem, BE_rmemt -> false
    | BE_rmemt, BE_wmem -> false
    | BE_wmem, BE_rmemt -> false
    | BE_rmem, BE_config -> false
    | BE_config, BE_rmem -> false
    | BE_rmem, BE_escape -> false
    | BE_escape, BE_rmem -> false
    | BE_rmem, BE_nondet -> false
    | BE_nondet, BE_rmem -> false
    | BE_rmem, BE_unspec -> false
    | BE_unspec, BE_rmem -> false
    | BE_rmem, BE_undef -> false
    | BE_undef, BE_rmem -> false
    | BE_rmem, BE_depend -> false
    | BE_depend, BE_rmem -> false
    | BE_rmem, BE_barr -> false
    | BE_barr, BE_rmem -> false
    | BE_rmem, BE_wmvt -> false
    | BE_wmvt, BE_rmem -> false
    | BE_rmem, BE_wmv -> false
    | BE_wmv, BE_rmem -> false
    | BE_rmem, BE_exmem -> false
    | BE_exmem, BE_rmem -> false
    | BE_rmem, BE_eamem -> false
    | BE_eamem, BE_rmem -> false
    | BE_rmem, BE_wmem -> false
    | BE_wmem, BE_rmem -> false
    | BE_rmem, BE_rmemt -> false
    | BE_rmemt, BE_rmem -> false
    | BE_wreg, BE_config -> false
    | BE_config, BE_wreg -> false
    | BE_wreg, BE_escape -> false
    | BE_escape, BE_wreg -> false
    | BE_wreg, BE_nondet -> false
    | BE_nondet, BE_wreg -> false
    | BE_wreg, BE_unspec -> false
    | BE_unspec, BE_wreg -> false
    | BE_wreg, BE_undef -> false
    | BE_undef, BE_wreg -> false
    | BE_wreg, BE_depend -> false
    | BE_depend, BE_wreg -> false
    | BE_wreg, BE_barr -> false
    | BE_barr, BE_wreg -> false
    | BE_wreg, BE_wmvt -> false
    | BE_wmvt, BE_wreg -> false
    | BE_wreg, BE_wmv -> false
    | BE_wmv, BE_wreg -> false
    | BE_wreg, BE_exmem -> false
    | BE_exmem, BE_wreg -> false
    | BE_wreg, BE_eamem -> false
    | BE_eamem, BE_wreg -> false
    | BE_wreg, BE_wmem -> false
    | BE_wmem, BE_wreg -> false
    | BE_wreg, BE_rmemt -> false
    | BE_rmemt, BE_wreg -> false
    | BE_wreg, BE_rmem -> false
    | BE_rmem, BE_wreg -> false
    | BE_rreg, BE_config -> false
    | BE_config, BE_rreg -> false
    | BE_rreg, BE_escape -> false
    | BE_escape, BE_rreg -> false
    | BE_rreg, BE_nondet -> false
    | BE_nondet, BE_rreg -> false
    | BE_rreg, BE_unspec -> false
    | BE_unspec, BE_rreg -> false
    | BE_rreg, BE_undef -> false
    | BE_undef, BE_rreg -> false
    | BE_rreg, BE_depend -> false
    | BE_depend, BE_rreg -> false
    | BE_rreg, BE_barr -> false
    | BE_barr, BE_rreg -> false
    | BE_rreg, BE_wmvt -> false
    | BE_wmvt, BE_rreg -> false
    | BE_rreg, BE_wmv -> false
    | BE_wmv, BE_rreg -> false
    | BE_rreg, BE_exmem -> false
    | BE_exmem, BE_rreg -> false
    | BE_rreg, BE_eamem -> false
    | BE_eamem, BE_rreg -> false
    | BE_rreg, BE_wmem -> false
    | BE_wmem, BE_rreg -> false
    | BE_rreg, BE_rmemt -> false
    | BE_rmemt, BE_rreg -> false
    | BE_rreg, BE_rmem -> false
    | BE_rmem, BE_rreg -> false
    | BE_rreg, BE_wreg -> false
    | BE_wreg, BE_rreg -> false
    | BE_config, BE_config -> true
    | BE_escape, BE_escape -> true
    | BE_nondet, BE_nondet -> true
    | BE_unspec, BE_unspec -> true
    | BE_undef, BE_undef -> true
    | BE_depend, BE_depend -> true
    | BE_barr, BE_barr -> true
    | BE_wmvt, BE_wmvt -> true
    | BE_wmv, BE_wmv -> true
    | BE_exmem, BE_exmem -> true
    | BE_eamem, BE_eamem -> true
    | BE_wmem, BE_wmem -> true
    | BE_rmemt, BE_rmemt -> true
    | BE_rmem, BE_rmem -> true
    | BE_wreg, BE_wreg -> true
    | BE_rreg, BE_rreg -> true;;

let equal_base_effect =
  ({HOL.equal = equal_base_effecta} : base_effect HOL.equal);;

let rec equal_effect
  (Effect_set x) (Effect_set ya) = Lista.equal_lista equal_base_effect x ya;;

let rec equal_kind x0 x1 = match x0, x1 with K_order, K_bool -> false
                     | K_bool, K_order -> false
                     | K_int, K_bool -> false
                     | K_bool, K_int -> false
                     | K_int, K_order -> false
                     | K_order, K_int -> false
                     | K_type, K_bool -> false
                     | K_bool, K_type -> false
                     | K_type, K_order -> false
                     | K_order, K_type -> false
                     | K_type, K_int -> false
                     | K_int, K_type -> false
                     | K_bool, K_bool -> true
                     | K_order, K_order -> true
                     | K_int, K_int -> true
                     | K_type, K_type -> true;;

let rec equal_kinded_ida
  (KOpt_kind (x1, x2)) (KOpt_kind (y1, y2)) =
    equal_kind x1 y1 && equal_kid x2 y2;;

let equal_kinded_id = ({HOL.equal = equal_kinded_ida} : kinded_id HOL.equal);;

let rec equal_typ () = ({HOL.equal = equal_typa} : typ HOL.equal)
and equal_typa
  x0 x1 = match x0, x1 with
    Typ_app (x71, x72), Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_app (x71, x72) -> false
    | Typ_tup x6, Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_tup x6 -> false
    | Typ_tup x6, Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_tup x6 -> false
    | Typ_bidir (x51, x52, x53), Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_tup x6 -> false
    | Typ_tup x6, Typ_bidir (x51, x52, x53) -> false
    | Typ_fn (x41, x42, x43), Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_tup x6 -> false
    | Typ_tup x6, Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_fn (x41, x42, x43) -> false
    | Typ_var x3, Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_var x3 -> false
    | Typ_var x3, Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_var x3 -> false
    | Typ_var x3, Typ_tup x6 -> false
    | Typ_tup x6, Typ_var x3 -> false
    | Typ_var x3, Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_var x3 -> false
    | Typ_var x3, Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_var x3 -> false
    | Typ_id x2, Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_id x2 -> false
    | Typ_id x2, Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_id x2 -> false
    | Typ_id x2, Typ_tup x6 -> false
    | Typ_tup x6, Typ_id x2 -> false
    | Typ_id x2, Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_id x2 -> false
    | Typ_id x2, Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_id x2 -> false
    | Typ_id x2, Typ_var x3 -> false
    | Typ_var x3, Typ_id x2 -> false
    | Typ_internal_unknown, Typ_exist (x81, x82, x83) -> false
    | Typ_exist (x81, x82, x83), Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_app (x71, x72) -> false
    | Typ_app (x71, x72), Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_tup x6 -> false
    | Typ_tup x6, Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_bidir (x51, x52, x53) -> false
    | Typ_bidir (x51, x52, x53), Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_fn (x41, x42, x43) -> false
    | Typ_fn (x41, x42, x43), Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_var x3 -> false
    | Typ_var x3, Typ_internal_unknown -> false
    | Typ_internal_unknown, Typ_id x2 -> false
    | Typ_id x2, Typ_internal_unknown -> false
    | Typ_exist (x81, x82, x83), Typ_exist (y81, y82, y83) ->
        Lista.equal_lista equal_kinded_id x81 y81 &&
          (equal_n_constraint x82 y82 && equal_typa x83 y83)
    | Typ_app (x71, x72), Typ_app (y71, y72) ->
        equal_ida x71 y71 && Lista.equal_lista (equal_typ_arg ()) x72 y72
    | Typ_tup x6, Typ_tup y6 -> Lista.equal_lista (equal_typ ()) x6 y6
    | Typ_bidir (x51, x52, x53), Typ_bidir (y51, y52, y53) ->
        equal_typa x51 y51 && (equal_typa x52 y52 && equal_effect x53 y53)
    | Typ_fn (x41, x42, x43), Typ_fn (y41, y42, y43) ->
        Lista.equal_lista (equal_typ ()) x41 y41 &&
          (equal_typa x42 y42 && equal_effect x43 y43)
    | Typ_var x3, Typ_var y3 -> equal_kid x3 y3
    | Typ_id x2, Typ_id y2 -> equal_ida x2 y2
    | Typ_internal_unknown, Typ_internal_unknown -> true
and equal_typ_arga x0 x1 = match x0, x1 with A_order x3, A_bool x4 -> false
                     | A_bool x4, A_order x3 -> false
                     | A_typ x2, A_bool x4 -> false
                     | A_bool x4, A_typ x2 -> false
                     | A_typ x2, A_order x3 -> false
                     | A_order x3, A_typ x2 -> false
                     | A_nexp x1, A_bool x4 -> false
                     | A_bool x4, A_nexp x1 -> false
                     | A_nexp x1, A_order x3 -> false
                     | A_order x3, A_nexp x1 -> false
                     | A_nexp x1, A_typ x2 -> false
                     | A_typ x2, A_nexp x1 -> false
                     | A_bool x4, A_bool y4 -> equal_n_constraint x4 y4
                     | A_order x3, A_order y3 -> equal_order x3 y3
                     | A_typ x2, A_typ y2 -> equal_typa x2 y2
                     | A_nexp x1, A_nexp y1 -> equal_nexpa x1 y1
and equal_typ_arg () = ({HOL.equal = equal_typ_arga} : typ_arg HOL.equal)
and equal_n_constraint
  x0 x1 = match x0, x1 with NC_true, NC_false -> false
    | NC_false, NC_true -> false
    | NC_var x11a, NC_false -> false
    | NC_false, NC_var x11a -> false
    | NC_var x11a, NC_true -> false
    | NC_true, NC_var x11a -> false
    | NC_app (x101, x102), NC_false -> false
    | NC_false, NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_true -> false
    | NC_true, NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_var x11a -> false
    | NC_var x11a, NC_app (x101, x102) -> false
    | NC_and (x91, x92), NC_false -> false
    | NC_false, NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_true -> false
    | NC_true, NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_var x11a -> false
    | NC_var x11a, NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_and (x91, x92) -> false
    | NC_or (x81, x82), NC_false -> false
    | NC_false, NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_true -> false
    | NC_true, NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_var x11a -> false
    | NC_var x11a, NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_or (x81, x82) -> false
    | NC_set (x71, x72), NC_false -> false
    | NC_false, NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_true -> false
    | NC_true, NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_var x11a -> false
    | NC_var x11a, NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_set (x71, x72) -> false
    | NC_not_equal (x61, x62), NC_false -> false
    | NC_false, NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_true -> false
    | NC_true, NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_var x11a -> false
    | NC_var x11a, NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_not_equal (x61, x62) -> false
    | NC_bounded_lt (x51, x52), NC_false -> false
    | NC_false, NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_true -> false
    | NC_true, NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_var x11a -> false
    | NC_var x11a, NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_le (x41, x42), NC_false -> false
    | NC_false, NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_true -> false
    | NC_true, NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_var x11a -> false
    | NC_var x11a, NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_bounded_le (x41, x42) -> false
    | NC_bounded_gt (x31, x32), NC_false -> false
    | NC_false, NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_true -> false
    | NC_true, NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_var x11a -> false
    | NC_var x11a, NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_ge (x21, x22), NC_false -> false
    | NC_false, NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_true -> false
    | NC_true, NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_var x11a -> false
    | NC_var x11a, NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_bounded_ge (x21, x22) -> false
    | NC_equal (x11, x12), NC_false -> false
    | NC_false, NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_true -> false
    | NC_true, NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_var x11a -> false
    | NC_var x11a, NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_app (x101, x102) -> false
    | NC_app (x101, x102), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_and (x91, x92) -> false
    | NC_and (x91, x92), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_or (x81, x82) -> false
    | NC_or (x81, x82), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_set (x71, x72) -> false
    | NC_set (x71, x72), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_not_equal (x61, x62) -> false
    | NC_not_equal (x61, x62), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_bounded_lt (x51, x52) -> false
    | NC_bounded_lt (x51, x52), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_bounded_le (x41, x42) -> false
    | NC_bounded_le (x41, x42), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_bounded_gt (x31, x32) -> false
    | NC_bounded_gt (x31, x32), NC_equal (x11, x12) -> false
    | NC_equal (x11, x12), NC_bounded_ge (x21, x22) -> false
    | NC_bounded_ge (x21, x22), NC_equal (x11, x12) -> false
    | NC_var x11a, NC_var y11a -> equal_kid x11a y11a
    | NC_app (x101, x102), NC_app (y101, y102) ->
        equal_ida x101 y101 && Lista.equal_lista (equal_typ_arg ()) x102 y102
    | NC_and (x91, x92), NC_and (y91, y92) ->
        equal_n_constraint x91 y91 && equal_n_constraint x92 y92
    | NC_or (x81, x82), NC_or (y81, y82) ->
        equal_n_constraint x81 y81 && equal_n_constraint x82 y82
    | NC_set (x71, x72), NC_set (y71, y72) ->
        equal_kid x71 y71 && Lista.equal_lista Arith.equal_integer x72 y72
    | NC_not_equal (x61, x62), NC_not_equal (y61, y62) ->
        equal_nexpa x61 y61 && equal_nexpa x62 y62
    | NC_bounded_lt (x51, x52), NC_bounded_lt (y51, y52) ->
        equal_nexpa x51 y51 && equal_nexpa x52 y52
    | NC_bounded_le (x41, x42), NC_bounded_le (y41, y42) ->
        equal_nexpa x41 y41 && equal_nexpa x42 y42
    | NC_bounded_gt (x31, x32), NC_bounded_gt (y31, y32) ->
        equal_nexpa x31 y31 && equal_nexpa x32 y32
    | NC_bounded_ge (x21, x22), NC_bounded_ge (y21, y22) ->
        equal_nexpa x21 y21 && equal_nexpa x22 y22
    | NC_equal (x11, x12), NC_equal (y11, y12) ->
        equal_nexpa x11 y11 && equal_nexpa x12 y12
    | NC_false, NC_false -> true
    | NC_true, NC_true -> true;;
let equal_typ = equal_typ ();;
let equal_typ_arg = equal_typ_arg ();;

type type_union = Tu_ty_id of typ * id;;

type quant_item = QI_id of kinded_id | QI_constraint of n_constraint |
  QI_constant of kinded_id list;;

type typquant = TypQ_tq of quant_item list | TypQ_no_forall;;

type tannot_opt = Typ_annot_opt_none | Typ_annot_opt_some of typquant * typ;;

type effect_opt = Effect_opt_none | Effect_opt_effect of effect;;

type typ_pat = TP_wild | TP_var of kid | TP_app of id * typ_pat list;;

type lit = L_unit | L_zero | L_one | L_true | L_false | L_num of Z.t |
  L_hex of string | L_bin of string | L_string of string | L_undef |
  L_real of string;;

type 'a pat = P_lit of 'a * lit | P_wild of 'a | P_or of 'a * 'a pat * 'a pat |
  P_not of 'a * 'a pat | P_as of 'a * 'a pat * id | P_typ of 'a * typ * 'a pat |
  P_id of 'a * id | P_var of 'a * 'a pat * typ_pat |
  P_app of 'a * id * 'a pat list | P_vector of 'a * 'a pat list |
  P_vector_concat of 'a * 'a pat list | P_tup of 'a * 'a pat list |
  P_list of 'a * 'a pat list | P_cons of 'a * 'a pat * 'a pat |
  P_string_append of 'a * 'a pat list;;

type value = Val;;

type loop = While | Until;;

type 'a exp = E_block of 'a * 'a exp list | E_id of 'a * id | E_lit of 'a * lit
  | E_cast of 'a * typ * 'a exp | E_app of 'a * id * 'a exp list |
  E_app_infix of 'a * 'a exp * id * 'a exp | E_tuple of 'a * 'a exp list |
  E_if of 'a * 'a exp * 'a exp * 'a exp |
  E_loop of 'a * loop * 'a internal_loop_measure * 'a exp * 'a exp |
  E_for of 'a * id * 'a exp * 'a exp * 'a exp * order * 'a exp |
  E_vector of 'a * 'a exp list | E_vector_access of 'a * 'a exp * 'a exp |
  E_vector_subrange of 'a * 'a exp * 'a exp * 'a exp |
  E_vector_update of 'a * 'a exp * 'a exp * 'a exp |
  E_vector_update_subrange of 'a * 'a exp * 'a exp * 'a exp * 'a exp |
  E_vector_append of 'a * 'a exp * 'a exp | E_list of 'a * 'a exp list |
  E_cons of 'a * 'a exp * 'a exp | E_record of 'a * 'a fexp list |
  E_record_update of 'a * 'a exp * 'a fexp list | E_field of 'a * 'a exp * id |
  E_case of 'a * 'a exp * 'a pexp list | E_let of 'a * 'a letbind * 'a exp |
  E_assign of 'a * 'a lexp * 'a exp | E_sizeof of 'a * nexp |
  E_return of 'a * 'a exp | E_exit of 'a * 'a exp | E_ref of 'a * id |
  E_throw of 'a * 'a exp | E_try of 'a * 'a exp * 'a pexp list |
  E_assert of 'a * 'a exp * 'a exp | E_var of 'a * 'a lexp * 'a exp * 'a exp |
  E_internal_plet of 'a * 'a pat * 'a exp * 'a exp |
  E_internal_return of 'a * 'a exp | E_internal_value of 'a * value |
  E_constraint of 'a * n_constraint
and 'a fexp = FE_Fexp of 'a * id * 'a exp
and 'a lexp = LEXP_id of 'a * id | LEXP_deref of 'a * 'a exp |
  LEXP_memory of 'a * id * 'a exp list | LEXP_cast of 'a * typ * id |
  LEXP_tup of 'a * 'a lexp list | LEXP_vector_concat of 'a * 'a lexp list |
  LEXP_vector of 'a * 'a lexp * 'a exp |
  LEXP_vector_range of 'a * 'a lexp * 'a exp * 'a exp |
  LEXP_field of 'a * 'a lexp * id
and 'a pexp = Pat_exp of 'a * 'a pat * 'a exp |
  Pat_when of 'a * 'a pat * 'a exp * 'a exp
and 'a letbind = LB_val of 'a * 'a pat * 'a exp
and 'a internal_loop_measure = Measure_none | Measure_some of 'a exp;;

type 'a rec_opt = Rec_nonrec | Rec_rec | Rec_measure of 'a pat * 'a exp;;

type 'a mpat = MP_lit of 'a * lit | MP_id of 'a * id |
  MP_app of 'a * id * 'a mpat list | MP_vector of 'a * 'a mpat list |
  MP_vector_concat of 'a * 'a mpat list | MP_tup of 'a * 'a mpat list |
  MP_list of 'a * 'a mpat list | MP_cons of 'a * 'a mpat * 'a mpat |
  MP_string_append of 'a * 'a mpat list | MP_typ of 'a * 'a mpat * typ |
  MP_as of 'a * 'a mpat * id;;

type 'a mpexp = MPat_pat of 'a * 'a mpat | MPat_when of 'a * 'a mpat * 'a exp;;

type 'a mapcl = MCL_bidir of 'a * 'a mpexp * 'a mpexp |
  MCL_forwards of 'a * 'a mpexp * 'a exp |
  MCL_backwards of 'a * 'a mpexp * 'a exp;;

type 'a pexp_funcl = PEXP_funcl of 'a pexp;;

type 'a funcl = FCL_Funcl of 'a * id * 'a pexp_funcl;;

type 'a scattered_def =
  SD_function of 'a * 'a rec_opt * tannot_opt * effect_opt * id |
  SD_funcl of 'a * 'a funcl | SD_variant of 'a * id * typquant |
  SD_unioncl of 'a * id * type_union | SD_mapping of 'a * id * tannot_opt |
  SD_mapcl of 'a * id * 'a mapcl | SD_end of 'a * id;;

type 'a loop_measure = Loop of loop * 'a exp;;

type default_spec = DT_order of order;;

type typschm = TypSchm_ts of typquant * typ;;

type val_spec =
  VS_aux of (typschm * (id * ((string -> string option) * bool)));;

type index_range = BF_single of nexp | BF_range of nexp * nexp |
  BF_concat of index_range * index_range;;

type type_def_aux = TD_abbrev of id * typquant * typ_arg |
  TD_record of id * typquant * (typ * id) list * bool |
  TD_variant of id * typquant * type_union list * bool |
  TD_enum of id * id list * bool |
  TD_bitfield of id * typ * (id * index_range) list;;

type type_def = TD_aux of type_def_aux;;

type 'a reg_id = RI_id of 'a * id;;

type 'a alias_spec = AL_subreg of 'a * 'a reg_id * id |
  AL_bit of 'a * 'a reg_id * 'a exp |
  AL_slice of 'a * 'a reg_id * 'a exp * 'a exp |
  AL_concat of 'a * 'a reg_id * 'a reg_id;;

type 'a dec_spec = DEC_reg of 'a * effect * effect * typ * id |
  DEC_config of 'a * id * typ * 'a exp | DEC_alias of 'a * id * 'a alias_spec |
  DEC_typ_alias of 'a * typ * id * 'a alias_spec;;

type 'a mapdef = MD_mapping of 'a * id * tannot_opt * 'a mapcl list;;

type 'a fundef =
  FD_function of 'a * 'a rec_opt * tannot_opt * effect_opt * 'a funcl list;;

type prec = Infix | InfixL | InfixR;;

type 'a def = DEF_type of type_def | DEF_fundef of 'a fundef |
  DEF_mapdef of 'a mapdef | DEF_val of 'a letbind | DEF_spec of val_spec |
  DEF_fixity of prec * Z.t * id | DEF_overload of id * id list |
  DEF_default of default_spec | DEF_scattered of 'a scattered_def |
  DEF_measure of id * 'a pat * 'a exp |
  DEF_loop_measures of id * 'a loop_measure list | DEF_reg_dec of 'a dec_spec |
  DEF_internal_mutrec of 'a fundef list | DEF_pragma of string * string;;

let rec annot_e
  = function E_block (x11, x12) -> x11
    | E_id (x21, x22) -> x21
    | E_lit (x31, x32) -> x31
    | E_cast (x41, x42, x43) -> x41
    | E_app (x51, x52, x53) -> x51
    | E_app_infix (x61, x62, x63, x64) -> x61
    | E_tuple (x71, x72) -> x71
    | E_if (x81, x82, x83, x84) -> x81
    | E_loop (x91, x92, x93, x94, x95) -> x91
    | E_for (x101, x102, x103, x104, x105, x106, x107) -> x101
    | E_vector (x111, x112) -> x111
    | E_vector_access (x121, x122, x123) -> x121
    | E_vector_subrange (x131, x132, x133, x134) -> x131
    | E_vector_update (x141, x142, x143, x144) -> x141
    | E_vector_update_subrange (x151, x152, x153, x154, x155) -> x151
    | E_vector_append (x161, x162, x163) -> x161
    | E_list (x171, x172) -> x171
    | E_cons (x181, x182, x183) -> x181
    | E_record (x191, x192) -> x191
    | E_record_update (x201, x202, x203) -> x201
    | E_field (x211, x212, x213) -> x211
    | E_case (x221, x222, x223) -> x221
    | E_let (x231, x232, x233) -> x231
    | E_assign (x241, x242, x243) -> x241
    | E_sizeof (x251, x252) -> x251
    | E_return (x261, x262) -> x261
    | E_exit (x271, x272) -> x271
    | E_ref (x281, x282) -> x281
    | E_throw (x291, x292) -> x291
    | E_try (x301, x302, x303) -> x301
    | E_assert (x311, x312, x313) -> x311
    | E_var (x321, x322, x323, x324) -> x321
    | E_internal_plet (x331, x332, x333, x334) -> x331
    | E_internal_return (x341, x342) -> x341
    | E_internal_value (x351, x352) -> x351
    | E_constraint (x361, x362) -> x361;;

let rec annot_pat = function P_lit (x11, x12) -> x11
                    | P_wild x2 -> x2
                    | P_or (x31, x32, x33) -> x31
                    | P_not (x41, x42) -> x41
                    | P_as (x51, x52, x53) -> x51
                    | P_typ (x61, x62, x63) -> x61
                    | P_id (x71, x72) -> x71
                    | P_var (x81, x82, x83) -> x81
                    | P_app (x91, x92, x93) -> x91
                    | P_vector (x101, x102) -> x101
                    | P_vector_concat (x111, x112) -> x111
                    | P_tup (x121, x122) -> x121
                    | P_list (x131, x132) -> x131
                    | P_cons (x141, x142, x143) -> x141
                    | P_string_append (x151, x152) -> x151;;

let rec annot_lexp = function LEXP_id (x11, x12) -> x11
                     | LEXP_deref (x21, x22) -> x21
                     | LEXP_memory (x31, x32, x33) -> x31
                     | LEXP_cast (x41, x42, x43) -> x41
                     | LEXP_tup (x51, x52) -> x51
                     | LEXP_vector_concat (x61, x62) -> x61
                     | LEXP_vector (x71, x72, x73) -> x71
                     | LEXP_vector_range (x81, x82, x83, x84) -> x81
                     | LEXP_field (x91, x92, x93) -> x91;;

end;; (*struct SailAST*)

module Fun : sig
  val id : 'a -> 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module Env : sig
  type mut = Mutable | Immutable
  type 'a env_ext =
    Env_ext of
      (SailAST.id * (SailAST.typquant * SailAST.typ)) list *
        (SailAST.kid * SailAST.kind) list *
        (SailAST.id * (mut * SailAST.typ)) list *
        (SailAST.id *
          (SailAST.typquant * (SailAST.id * SailAST.typ) list)) list *
        (SailAST.id * (SailAST.typquant * SailAST.type_union list)) list *
        SailAST.n_constraint list * SailAST.order option * SailAST.typ option *
        (SailAST.id * SailAST.typ) list *
        (SailAST.id * (SailAST.typquant * SailAST.typ_arg)) list *
        (SailAST.id * SailAST.id list) list *
        (SailAST.n_constraint list -> SailAST.n_constraint -> bool) option * 'a
  type 'a tannot_ext =
    Tannot_ext of
      unit env_ext * SailAST.typ * SailAST.effect * SailAST.typ option *
        ((SailAST.kid * SailAST.typ_arg) list) option * 'a
  val tannot_typ : 'a tannot_ext -> SailAST.typ
  val tannot_env : 'a tannot_ext -> unit env_ext
  val get : unit tannot_ext option -> (unit env_ext * SailAST.typ) option
  val bind : ('a -> 'b) -> 'a option -> 'b option
  val get_e :
    (unit tannot_ext option) SailAST.exp -> (unit env_ext * SailAST.typ) option
  val constraints : 'a env_ext -> SailAST.n_constraint list
  val prover :
    'a env_ext ->
      (SailAST.n_constraint list -> SailAST.n_constraint -> bool) option
  val prove : unit env_ext -> SailAST.n_constraint -> bool
  val lookup : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
  val get_env : unit tannot_ext option -> unit env_ext option
  val emptyEnv : unit env_ext
  val get_type : unit tannot_ext option -> SailAST.typ option
  val ret_typ : 'a env_ext -> SailAST.typ option
  val ret_type : unit tannot_ext option -> SailAST.typ option
  val subst_order :
    SailAST.kid * SailAST.typ_arg -> SailAST.order -> SailAST.order
  val subst_nexp : SailAST.kid * SailAST.typ_arg -> SailAST.nexp -> SailAST.nexp
  val subst_nc :
    SailAST.kid * SailAST.typ_arg ->
      SailAST.n_constraint -> SailAST.n_constraint
  val subst_typ_arg :
    SailAST.kid * SailAST.typ_arg -> SailAST.typ_arg -> SailAST.typ_arg
  val subst_typ : SailAST.kid * SailAST.typ_arg -> SailAST.typ -> SailAST.typ
  val enums : 'a env_ext -> (SailAST.id * SailAST.id list) list
  val get_tan_e : (unit tannot_ext option) SailAST.exp -> unit tannot_ext option
  val registers : 'a env_ext -> (SailAST.id * SailAST.typ) list
  val lookup_register_env : unit env_ext -> SailAST.id -> SailAST.typ option
  val lookup_register :
    unit tannot_ext option -> SailAST.id -> SailAST.typ option
  val lookup_enum_env : unit env_ext -> SailAST.id -> SailAST.typ option
  val locals : 'a env_ext -> (SailAST.id * (mut * SailAST.typ)) list
  val lookup_local_id_env : unit env_ext -> SailAST.id -> SailAST.typ option
  val lookup_local_id :
    unit tannot_ext option -> SailAST.id -> SailAST.typ option
  val lookup_id : unit tannot_ext option -> SailAST.id -> SailAST.typ option
  val top_val_specs :
    'a env_ext -> (SailAST.id * (SailAST.typquant * SailAST.typ)) list
  val get_val_spec_env :
    unit env_ext -> SailAST.id -> (SailAST.typquant * SailAST.typ) option
  val lookup_fun :
    unit tannot_ext option ->
      SailAST.id -> (SailAST.typ list * SailAST.typ) option
  val lookup_tud : SailAST.type_union list -> SailAST.id -> SailAST.typ option
  val tannot_instantiations :
    'a tannot_ext -> ((SailAST.kid * SailAST.typ_arg) list) option
  val subst_inst : unit tannot_ext option -> SailAST.typ -> SailAST.typ option
  val records :
    'a env_ext ->
      (SailAST.id * (SailAST.typquant * (SailAST.id * SailAST.typ) list)) list
  val get_env_exp : (unit tannot_ext option) SailAST.exp -> unit env_ext option
  val get_tan_pat :
    (unit tannot_ext option) SailAST.pat -> unit tannot_ext option
  val lookup_enum : unit tannot_ext option -> SailAST.id -> SailAST.typ option
  val type_of_exp : (unit tannot_ext option) SailAST.exp -> SailAST.typ option
  val type_of_pat : (unit tannot_ext option) SailAST.pat -> SailAST.typ option
  val typ_vars : 'a env_ext -> (SailAST.kid * SailAST.kind) list
  val variants :
    'a env_ext ->
      (SailAST.id * (SailAST.typquant * SailAST.type_union list)) list
  val get_tan_lexp :
    (unit tannot_ext option) SailAST.lexp -> unit tannot_ext option
  val is_list_type : unit tannot_ext option -> SailAST.typ option
  val lookup_index : (SailAST.id * 'a) list -> SailAST.id -> Arith.nat option
  val type_of_lexp : (unit tannot_ext option) SailAST.lexp -> SailAST.typ option
  val type_of_pexp : (unit tannot_ext option) SailAST.pexp -> SailAST.typ option
  val constraints_update :
    (SailAST.n_constraint list -> SailAST.n_constraint list) ->
      'a env_ext -> 'a env_ext
  val add_constraint : SailAST.n_constraint -> unit env_ext -> unit env_ext
  val deconstruct_bitvector_type :
    SailAST.typ -> (SailAST.nexp * (SailAST.order * SailAST.typ)) option
  val deconstruct_vector_type :
    SailAST.typ -> (SailAST.nexp * (SailAST.order * SailAST.typ)) option
  val is_vector_type :
    unit tannot_ext option ->
      (SailAST.nexp * (SailAST.order * SailAST.typ)) option
  val lookup_mutable_env : unit env_ext -> SailAST.id -> SailAST.typ option
  val lookup_mutable :
    unit tannot_ext option -> SailAST.id -> SailAST.typ option
  val subst_inst_list :
    unit tannot_ext option -> SailAST.typ list -> (SailAST.typ list) option
  val typ_synonyms :
    'a env_ext -> (SailAST.id * (SailAST.typquant * SailAST.typ_arg)) list
  val lookup_variant_env :
    unit env_ext -> SailAST.id -> SailAST.id -> SailAST.typ option
  val deconstruct_bool_type : SailAST.typ -> SailAST.n_constraint option
  val deconstruct_record_type : SailAST.typ -> SailAST.id option
  val lookup_record_field_env :
    unit env_ext -> SailAST.id -> SailAST.id -> SailAST.typ option
  val deconstruct_register_type : SailAST.typ -> SailAST.typ option
  val lookup_register_index_env : unit env_ext -> SailAST.id -> Arith.nat option
end = struct

type mut = Mutable | Immutable;;

type 'a env_ext =
  Env_ext of
    (SailAST.id * (SailAST.typquant * SailAST.typ)) list *
      (SailAST.kid * SailAST.kind) list *
      (SailAST.id * (mut * SailAST.typ)) list *
      (SailAST.id * (SailAST.typquant * (SailAST.id * SailAST.typ) list)) list *
      (SailAST.id * (SailAST.typquant * SailAST.type_union list)) list *
      SailAST.n_constraint list * SailAST.order option * SailAST.typ option *
      (SailAST.id * SailAST.typ) list *
      (SailAST.id * (SailAST.typquant * SailAST.typ_arg)) list *
      (SailAST.id * SailAST.id list) list *
      (SailAST.n_constraint list -> SailAST.n_constraint -> bool) option * 'a;;

type 'a tannot_ext =
  Tannot_ext of
    unit env_ext * SailAST.typ * SailAST.effect * SailAST.typ option *
      ((SailAST.kid * SailAST.typ_arg) list) option * 'a;;

let rec tannot_typ
  (Tannot_ext
    (tannot_env, tannot_typ, tannot_effect, tannot_expected,
      tannot_instantiations, more))
    = tannot_typ;;

let rec tannot_env
  (Tannot_ext
    (tannot_env, tannot_typ, tannot_effect, tannot_expected,
      tannot_instantiations, more))
    = tannot_env;;

let rec get = function None -> None
              | Some tan -> Some (tannot_env tan, tannot_typ tan);;

let rec bind f t = Option.bind t (Fun.comp (fun a -> Some a) f);;

let rec get_e exp = get (SailAST.annot_e exp);;

let rec constraints
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = constraints;;

let rec prover
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = prover;;

let rec prove
  env nc =
    (match prover env with None -> true | Some p -> p (constraints env) nc);;

let rec lookup _A
  x0 uu = match x0, uu with [], uu -> None
    | (x, t) :: xs, y -> (if HOL.eq _A x y then Some t else lookup _A xs y);;

let rec get_env x = bind tannot_env x;;

let emptyEnv : unit env_ext
  = Env_ext ([], [], [], [], [], [], None, None, [], [], [], None, ());;

let rec get_type x = bind tannot_typ x;;

let rec ret_typ
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = ret_typ;;

let rec ret_type
  t = Option.bind (Option.bind t (Fun.comp (fun a -> Some a) tannot_env))
        ret_typ;;

let rec subst_order
  uv x1 = match uv, x1 with
    (k1, SailAST.A_order ord), SailAST.Ord_var k2 ->
      (if SailAST.equal_kid k1 k2 then ord else SailAST.Ord_var k2)
    | (k1, SailAST.A_nexp v), SailAST.Ord_var k2 -> SailAST.Ord_var k2
    | (k1, SailAST.A_typ v), SailAST.Ord_var k2 -> SailAST.Ord_var k2
    | (k1, SailAST.A_bool v), SailAST.Ord_var k2 -> SailAST.Ord_var k2
    | uv, SailAST.Ord_inc -> SailAST.Ord_inc
    | uw, SailAST.Ord_dec -> SailAST.Ord_dec;;

let rec subst_nexp
  ks x1 = match ks, x1 with ks, SailAST.Nexp_id x -> SailAST.Nexp_id x
    | (k1, SailAST.A_nexp ne), SailAST.Nexp_var k2 ->
        (if SailAST.equal_kid k1 k2 then ne else SailAST.Nexp_var k2)
    | (k1, SailAST.A_bool uu), SailAST.Nexp_var k2 -> SailAST.Nexp_var k2
    | (k1, SailAST.A_typ uv), SailAST.Nexp_var k2 -> SailAST.Nexp_var k2
    | (k1, SailAST.A_order uw), SailAST.Nexp_var k2 -> SailAST.Nexp_var k2
    | ks, SailAST.Nexp_constant n -> SailAST.Nexp_constant n
    | ks, SailAST.Nexp_app (x, nes) ->
        SailAST.Nexp_app (x, Lista.map (subst_nexp ks) nes)
    | ks, SailAST.Nexp_times (n1, n2) ->
        SailAST.Nexp_times (subst_nexp ks n1, subst_nexp ks n1)
    | ks, SailAST.Nexp_sum (n1, n2) ->
        SailAST.Nexp_sum (subst_nexp ks n1, subst_nexp ks n1)
    | ks, SailAST.Nexp_minus (n1, n2) ->
        SailAST.Nexp_minus (subst_nexp ks n1, subst_nexp ks n1)
    | ks, SailAST.Nexp_exp n1 -> SailAST.Nexp_exp (subst_nexp ks n1)
    | ks, SailAST.Nexp_neg n1 -> SailAST.Nexp_neg (subst_nexp ks n1);;

let rec subst_nc
  ks x1 = match ks, x1 with
    ks, SailAST.NC_equal (ne1, ne2) ->
      SailAST.NC_equal (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_bounded_ge (ne1, ne2) ->
        SailAST.NC_bounded_ge (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_bounded_gt (ne1, ne2) ->
        SailAST.NC_bounded_gt (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_bounded_le (ne1, ne2) ->
        SailAST.NC_bounded_le (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_bounded_lt (ne1, ne2) ->
        SailAST.NC_bounded_lt (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_not_equal (ne1, ne2) ->
        SailAST.NC_not_equal (subst_nexp ks ne1, subst_nexp ks ne1)
    | ks, SailAST.NC_set (k, is) -> SailAST.NC_set (k, is)
    | ks, SailAST.NC_or (nc1, nc2) ->
        SailAST.NC_or (subst_nc ks nc1, subst_nc ks nc2)
    | ks, SailAST.NC_and (nc1, nc2) ->
        SailAST.NC_and (subst_nc ks nc1, subst_nc ks nc2)
    | ks, SailAST.NC_app (tid, args) ->
        SailAST.NC_app (tid, Lista.map (subst_typ_arg ks) args)
    | (k1, SailAST.A_bool nc), SailAST.NC_var k2 ->
        (if SailAST.equal_kid k1 k2 then nc else SailAST.NC_var k2)
    | (k1, SailAST.A_nexp uu), SailAST.NC_var k2 -> SailAST.NC_var k2
    | (k1, SailAST.A_typ uv), SailAST.NC_var k2 -> SailAST.NC_var k2
    | (k1, SailAST.A_order uw), SailAST.NC_var k2 -> SailAST.NC_var k2
    | ks, SailAST.NC_true -> SailAST.NC_true
    | ks, SailAST.NC_false -> SailAST.NC_false
and subst_typ_arg
  ks x1 = match ks, x1 with
    ks, SailAST.A_nexp ne -> SailAST.A_nexp (subst_nexp ks ne)
    | ks, SailAST.A_typ ne -> SailAST.A_typ (subst_typ ks ne)
    | ks, SailAST.A_order ne -> SailAST.A_order (subst_order ks ne)
    | ks, SailAST.A_bool nc -> SailAST.A_bool (subst_nc ks nc)
and subst_typ
  ux x1 = match ux, x1 with
    ux, SailAST.Typ_internal_unknown -> SailAST.Typ_internal_unknown
    | uy, SailAST.Typ_id tyid -> SailAST.Typ_id tyid
    | (k1, SailAST.A_typ t), SailAST.Typ_var k2 ->
        (if SailAST.equal_kid k1 k2 then t else SailAST.Typ_var k2)
    | (k1, SailAST.A_bool uz), SailAST.Typ_var k2 -> SailAST.Typ_var k2
    | (k1, SailAST.A_order va), SailAST.Typ_var k2 -> SailAST.Typ_var k2
    | (k1, SailAST.A_nexp vb), SailAST.Typ_var k2 -> SailAST.Typ_var k2
    | ks, SailAST.Typ_fn (ts, tr, e) ->
        SailAST.Typ_fn (Lista.map (subst_typ ks) ts, subst_typ ks tr, e)
    | ks, SailAST.Typ_bidir (t1, t2, e) ->
        SailAST.Typ_bidir (subst_typ ks t1, subst_typ ks t2, e)
    | ks, SailAST.Typ_tup ts -> SailAST.Typ_tup (Lista.map (subst_typ ks) ts)
    | ks, SailAST.Typ_app (tyid, tas) ->
        SailAST.Typ_app (tyid, Lista.map (subst_typ_arg ks) tas)
    | ks, SailAST.Typ_exist (kids, nc, typ) ->
        SailAST.Typ_exist (kids, subst_nc ks nc, subst_typ ks typ);;

let rec enums
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = enums;;

let rec get_tan_e exp = SailAST.annot_e exp;;

let rec registers
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = registers;;

let rec lookup_register_env
  env x =
    (match lookup SailAST.equal_id (registers env) x with None -> None
      | Some a -> Some a);;

let rec lookup_register
  xa0 x = match xa0, x with
    Some tan, x -> lookup_register_env (tannot_env tan) x
    | None, uu -> None;;

let rec lookup_enum_env
  env x =
    (match
      Lista.find (fun (_, es) -> Lista.member SailAST.equal_id es x) (enums env)
      with None -> None | Some (tyid, _) -> Some (SailAST.Typ_id tyid));;

let rec locals
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = locals;;

let rec lookup_local_id_env
  env x =
    (match lookup SailAST.equal_id (locals env) x
      with None -> lookup_enum_env env x
      | Some a -> (let (_, aa) = a in Some aa));;

let rec lookup_local_id
  xa0 x = match xa0, x with
    Some tan, x -> lookup_local_id_env (tannot_env tan) x
    | None, x -> None;;

let rec lookup_id
  t x = (match lookup_local_id t x with None -> lookup_register t x
          | Some a -> Some a);;

let rec top_val_specs
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = top_val_specs;;

let rec get_val_spec_env env x = lookup SailAST.equal_id (top_val_specs env) x;;

let rec lookup_fun
  x0 fid = match x0, fid with
    Some tan, fid ->
      (match get_val_spec_env (tannot_env tan) fid with None -> None
        | Some (_, SailAST.Typ_internal_unknown) -> None
        | Some (_, SailAST.Typ_id _) -> None
        | Some (_, SailAST.Typ_var _) -> None
        | Some (_, SailAST.Typ_fn (in_typs, rett_typ, _)) ->
          Some (in_typs, rett_typ)
        | Some (_, SailAST.Typ_bidir (_, _, _)) -> None
        | Some (_, SailAST.Typ_tup _) -> None
        | Some (_, SailAST.Typ_app (_, _)) -> None
        | Some (_, SailAST.Typ_exist (_, _, _)) -> None)
    | None, uu -> None;;

let rec lookup_tud
  x0 uu = match x0, uu with [], uu -> None
    | SailAST.Tu_ty_id (typ, SailAST.Id x) :: tus, SailAST.Id y ->
        (if ((x : string) = y) then Some typ else lookup_tud tus (SailAST.Id y))
    | SailAST.Tu_ty_id (v, SailAST.Operator vb) :: tus, uw -> None
    | uv :: tus, SailAST.Operator v -> None;;

let rec tannot_instantiations
  (Tannot_ext
    (tannot_env, tannot_typ, tannot_effect, tannot_expected,
      tannot_instantiations, more))
    = tannot_instantiations;;

let rec subst_inst
  x0 t = match x0, t with None, t -> Some t
    | Some ta, t ->
        (match tannot_instantiations ta with None -> Some t
          | Some is -> Some (Lista.fold subst_typ is t));;

let rec records
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = records;;

let rec get_env_exp exp = get_env (get_tan_e exp);;

let rec get_tan_pat exp = SailAST.annot_pat exp;;

let rec lookup_enum
  xa0 x = match xa0, x with Some tan, x -> lookup_enum_env (tannot_env tan) x
    | None, uu -> None;;

let rec type_of_exp exp = get_type (get_tan_e exp);;

let rec type_of_pat pat = get_type (get_tan_pat pat);;

let rec typ_vars
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = typ_vars;;

let rec variants
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = variants;;

let rec get_tan_lexp lexp = SailAST.annot_lexp lexp;;

let rec is_list_type
  = function None -> None
    | Some t ->
        (match tannot_typ t with SailAST.Typ_internal_unknown -> None
          | SailAST.Typ_id _ -> None | SailAST.Typ_var _ -> None
          | SailAST.Typ_fn (_, _, _) -> None
          | SailAST.Typ_bidir (_, _, _) -> None | SailAST.Typ_tup _ -> None
          | SailAST.Typ_app (SailAST.Id _, []) -> None
          | SailAST.Typ_app (SailAST.Id _, SailAST.A_nexp _ :: _) -> None
          | SailAST.Typ_app (SailAST.Id app_id, [SailAST.A_typ typ]) ->
            (if ((app_id : string) = "list") then Some typ else None)
          | SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _ :: _) -> None
          | SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _) -> None
          | SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _) -> None
          | SailAST.Typ_app (SailAST.Operator _, _) -> None
          | SailAST.Typ_exist (_, _, _) -> None);;

let rec lookup_index
  x0 uu = match x0, uu with [], uu -> None
    | x :: xs, y ->
        (if SailAST.equal_ida (Product_Type.fst x) y
          then Some (Lista.size_list xs) else lookup_index xs y);;

let rec type_of_lexp lexp = get_type (get_tan_lexp lexp);;

let rec type_of_pexp
  = function SailAST.Pat_exp (uu, pat, exp) -> type_of_pat pat
    | SailAST.Pat_when (uv, pat, uw, exp) -> type_of_pat pat;;

let rec constraints_update
  constraintsa
    (Env_ext
      (top_val_specs, typ_vars, locals, records, variants, constraints,
        default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = Env_ext
        (top_val_specs, typ_vars, locals, records, variants,
          constraintsa constraints, default_order, ret_typ, registers,
          typ_synonyms, enums, prover, more);;

let rec add_constraint
  nc env = constraints_update (fun _ -> nc :: constraints env) env;;

let rec deconstruct_bitvector_type
  t = (match t with SailAST.Typ_internal_unknown -> None
        | SailAST.Typ_id _ -> None | SailAST.Typ_var _ -> None
        | SailAST.Typ_fn (_, _, _) -> None | SailAST.Typ_bidir (_, _, _) -> None
        | SailAST.Typ_tup _ -> None | SailAST.Typ_app (SailAST.Id _, []) -> None
        | SailAST.Typ_app (SailAST.Id _, [SailAST.A_nexp _]) -> None
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_nexp _ :: _)
          -> None
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_typ _ :: _)
          -> None
        | SailAST.Typ_app
            (SailAST.Id app_id, [SailAST.A_nexp len; SailAST.A_order ord])
          -> (if ((app_id : string) = "bitvector")
               then Some (len, (ord, SailAST.Typ_id (SailAST.Id "bit")))
               else None)
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_order _ :: _ :: _)
          -> None
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_bool _ :: _)
          -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _) -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _) -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _) -> None
        | SailAST.Typ_app (SailAST.Operator _, _) -> None
        | SailAST.Typ_exist (_, _, _) -> None);;

let rec deconstruct_vector_type
  t = (match t with SailAST.Typ_internal_unknown -> deconstruct_bitvector_type t
        | SailAST.Typ_id _ -> deconstruct_bitvector_type t
        | SailAST.Typ_var _ -> deconstruct_bitvector_type t
        | SailAST.Typ_fn (_, _, _) -> deconstruct_bitvector_type t
        | SailAST.Typ_bidir (_, _, _) -> deconstruct_bitvector_type t
        | SailAST.Typ_tup _ -> deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, []) -> deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, [SailAST.A_nexp _]) ->
          deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_nexp _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_typ _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_order _])
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _,
              SailAST.A_nexp _ :: SailAST.A_order _ :: SailAST.A_nexp _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id app_id,
              [SailAST.A_nexp len; SailAST.A_order ord; SailAST.A_typ typ])
          -> (if ((app_id : string) = "vector") then Some (len, (ord, typ))
               else None)
        | SailAST.Typ_app
            (SailAST.Id _,
              SailAST.A_nexp _ ::
                SailAST.A_order _ :: SailAST.A_typ _ :: _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _,
              SailAST.A_nexp _ :: SailAST.A_order _ :: SailAST.A_order _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _,
              SailAST.A_nexp _ :: SailAST.A_order _ :: SailAST.A_bool _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app
            (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_bool _ :: _)
          -> deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _) ->
          deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _) ->
          deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _) ->
          deconstruct_bitvector_type t
        | SailAST.Typ_app (SailAST.Operator _, _) ->
          deconstruct_bitvector_type t
        | SailAST.Typ_exist (_, _, _) -> deconstruct_bitvector_type t);;

let rec is_vector_type = function None -> None
                         | Some t -> deconstruct_vector_type (tannot_typ t);;

let rec lookup_mutable_env
  env x =
    (match lookup SailAST.equal_id (locals env) x
      with None -> lookup_register_env env x | Some (Mutable, t) -> Some t);;

let rec lookup_mutable
  xa0 x = match xa0, x with Some tan, x -> lookup_mutable_env (tannot_env tan) x
    | None, x -> None;;

let rec subst_inst_list
  tan typs = Lista.those (Lista.map (subst_inst tan) typs);;

let rec typ_synonyms
  (Env_ext
    (top_val_specs, typ_vars, locals, records, variants, constraints,
      default_order, ret_typ, registers, typ_synonyms, enums, prover, more))
    = typ_synonyms;;

let rec lookup_variant_env
  env tid vid =
    (match lookup SailAST.equal_id (variants env) tid with None -> None
      | Some (_, tus) -> lookup_tud tus vid);;

let rec deconstruct_bool_type
  = function
    SailAST.Typ_id (SailAST.Id b) ->
      (if ((b : string) = "bool") then Some SailAST.NC_true else None)
    | SailAST.Typ_app (SailAST.Id b, [SailAST.A_bool nc]) ->
        (if ((b : string) = "atom_bool") then Some nc else None)
    | SailAST.Typ_exist (kids, nc, typ) -> deconstruct_bool_type typ
    | SailAST.Typ_internal_unknown -> None
    | SailAST.Typ_id (SailAST.Operator va) -> None
    | SailAST.Typ_var v -> None
    | SailAST.Typ_fn (v, va, vb) -> None
    | SailAST.Typ_bidir (v, va, vb) -> None
    | SailAST.Typ_tup v -> None
    | SailAST.Typ_app (SailAST.Operator vb, va) -> None
    | SailAST.Typ_app (SailAST.Id va, []) -> None
    | SailAST.Typ_app (SailAST.Id va, SailAST.A_nexp vc :: vb) -> None
    | SailAST.Typ_app (SailAST.Id va, SailAST.A_typ vc :: vb) -> None
    | SailAST.Typ_app (SailAST.Id va, SailAST.A_order vc :: vb) -> None
    | SailAST.Typ_app (SailAST.Id va, v :: vc :: vd) -> None;;

let rec deconstruct_record_type = function SailAST.Typ_id recid -> Some recid
                                  | SailAST.Typ_app (recid, uu) -> Some recid
                                  | SailAST.Typ_internal_unknown -> None
                                  | SailAST.Typ_var v -> None
                                  | SailAST.Typ_fn (v, va, vb) -> None
                                  | SailAST.Typ_bidir (v, va, vb) -> None
                                  | SailAST.Typ_tup v -> None
                                  | SailAST.Typ_exist (v, va, vb) -> None;;

let rec lookup_record_field_env
  env recc_id field_id =
    (match lookup SailAST.equal_id (records env) recc_id with None -> None
      | Some (_, fieldds) -> lookup SailAST.equal_id fieldds field_id);;

let rec deconstruct_register_type
  t = (match t with SailAST.Typ_internal_unknown -> None
        | SailAST.Typ_id _ -> None | SailAST.Typ_var _ -> None
        | SailAST.Typ_fn (_, _, _) -> None | SailAST.Typ_bidir (_, _, _) -> None
        | SailAST.Typ_tup _ -> None | SailAST.Typ_app (SailAST.Id _, []) -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_nexp _ :: _) -> None
        | SailAST.Typ_app (SailAST.Id app_id, [SailAST.A_typ typ]) ->
          (if ((app_id : string) = "register") then Some typ else None)
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _ :: _) -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _) -> None
        | SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _) -> None
        | SailAST.Typ_app (SailAST.Operator _, _) -> None
        | SailAST.Typ_exist (_, _, _) -> None);;

let rec lookup_register_index_env
  env x =
    (match lookup_index (registers env) x with None -> None
      | Some a -> Some a);;

end;; (*struct Env*)

module Set : sig
  type 'a set = Set of 'a list | Coset of 'a list
  val insert : 'a HOL.equal -> 'a -> 'a set -> 'a set
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
  val bot_set : 'a set
  val sup_set : 'a HOL.equal -> 'a set -> 'a set -> 'a set
end = struct

type 'a set = Set of 'a list | Coset of 'a list;;

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

end;; (*struct Set*)

module FSet : sig
  type 'a fset = Abs_fset of 'a Set.set
  val bot_fset : 'a fset
end = struct

type 'a fset = Abs_fset of 'a Set.set;;

let bot_fset : 'a fset = Abs_fset Set.bot_set;;

end;; (*struct FSet*)

module Stringa : sig
  type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool
  val equal_chara : char -> char -> bool
  val equal_char : char HOL.equal
  val equal_literal : string HOL.equal
  val integer_of_char : char -> Z.t
  val implode : char list -> string
  val char_of_integer : Z.t -> char
  val explode : string -> char list
end = struct

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec equal_chara
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

let equal_char = ({HOL.equal = equal_chara} : char HOL.equal);;

let equal_literal =
  ({HOL.equal = (fun a b -> ((a : string) = b))} : string HOL.equal);;

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

end;; (*struct Stringa*)

module Show : sig
  type 'a show =
    {shows_prec : Arith.nat -> 'a -> Stringa.char list -> Stringa.char list;
      shows_list : 'a list -> Stringa.char list -> Stringa.char list}
  val shows_prec :
    'a show -> Arith.nat -> 'a -> Stringa.char list -> Stringa.char list
  val shows_list : 'a show -> 'a list -> Stringa.char list -> Stringa.char list
  val shows_prec_list :
    'a show -> Arith.nat -> 'a list -> Stringa.char list -> Stringa.char list
  val shows_string : Stringa.char list -> Stringa.char list -> Stringa.char list
  val shows_sep :
    ('a -> Stringa.char list -> Stringa.char list) ->
      (Stringa.char list -> Stringa.char list) ->
        'a list -> Stringa.char list -> Stringa.char list
  val shows_list_gen :
    ('a -> Stringa.char list -> Stringa.char list) ->
      Stringa.char list ->
        Stringa.char list ->
          Stringa.char list ->
            Stringa.char list ->
              'a list -> Stringa.char list -> Stringa.char list
  val showsp_list :
    (Arith.nat -> 'a -> Stringa.char list -> Stringa.char list) ->
      Arith.nat -> 'a list -> Stringa.char list -> Stringa.char list
  val shows_list_list :
    'a show -> ('a list) list -> Stringa.char list -> Stringa.char list
  val show_list : 'a show -> ('a list) show
  val shows_prec_char :
    Arith.nat -> Stringa.char -> Stringa.char list -> Stringa.char list
  val shows_pl : Arith.nat -> Stringa.char list -> Stringa.char list
  val shows_pr : Arith.nat -> Stringa.char list -> Stringa.char list
  val shows_space : Stringa.char list -> Stringa.char list
end = struct

type 'a show =
  {shows_prec : Arith.nat -> 'a -> Stringa.char list -> Stringa.char list;
    shows_list : 'a list -> Stringa.char list -> Stringa.char list};;
let shows_prec _A = _A.shows_prec;;
let shows_list _A = _A.shows_list;;

let rec shows_prec_list _A p xs = shows_list _A xs;;

let rec shows_string x = (fun a -> x @ a);;

let rec shows_sep
  s sep x2 = match s, sep, x2 with s, sep, [] -> shows_string []
    | s, sep, [x] -> s x
    | s, sep, x :: v :: va ->
        Fun.comp (Fun.comp (s x) sep) (shows_sep s sep (v :: va));;

let rec shows_list_gen
  showsx e l s r xs =
    (if Lista.null xs then shows_string e
      else Fun.comp
             (Fun.comp (shows_string l) (shows_sep showsx (shows_string s) xs))
             (shows_string r));;

let rec showsp_list
  s p xs =
    shows_list_gen (s Arith.Zero_nat)
      [Stringa.Chara (true, true, false, true, true, false, true, false);
        Stringa.Chara (true, false, true, true, true, false, true, false)]
      [Stringa.Chara (true, true, false, true, true, false, true, false)]
      [Stringa.Chara (false, false, true, true, false, true, false, false);
        Stringa.Chara (false, false, false, false, false, true, false, false)]
      [Stringa.Chara (true, false, true, true, true, false, true, false)] xs;;

let rec shows_list_list _A
  xss = showsp_list (shows_prec_list _A) Arith.Zero_nat xss;;

let rec show_list _A =
  ({shows_prec = shows_prec_list _A; shows_list = shows_list_list _A} :
    ('a list) show);;

let rec shows_prec_char p c = (fun a -> c :: a);;

let rec shows_pl
  p = (if Arith.less_nat Arith.Zero_nat p
        then shows_prec_char Arith.Zero_nat
               (Stringa.Chara
                 (false, false, false, true, false, true, false, false))
        else Fun.id);;

let rec shows_pr
  p = (if Arith.less_nat Arith.Zero_nat p
        then shows_prec_char Arith.Zero_nat
               (Stringa.Chara
                 (true, false, false, true, false, true, false, false))
        else Fun.id);;

let rec shows_space
  x = shows_prec_char Arith.Zero_nat
        (Stringa.Chara (false, false, false, false, false, true, false, false))
        x;;

end;; (*struct Show*)

module Utils : sig
  val string_of_digit : Arith.nat -> Stringa.char list
  val string_of_nat : Arith.nat -> Stringa.char list
end = struct

let rec string_of_digit
  n = (if Arith.equal_nat n Arith.Zero_nat
        then [Stringa.Chara
                (false, false, false, false, true, true, false, false)]
        else (if Arith.equal_nat n Arith.one_nat
               then [Stringa.Chara
                       (true, false, false, false, true, true, false, false)]
               else (if Arith.equal_nat n
                          (Arith.nat_of_num (Arith.Bit0 Arith.One))
                      then [Stringa.Chara
                              (false, true, false, false, true, true, false,
                                false)]
                      else (if Arith.equal_nat n
                                 (Arith.nat_of_num (Arith.Bit1 Arith.One))
                             then [Stringa.Chara
                                     (true, true, false, false, true, true,
                                       false, false)]
                             else (if Arith.equal_nat n
(Arith.nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One)))
                                    then [Stringa.Chara
    (false, false, true, false, true, true, false, false)]
                                    else (if Arith.equal_nat n
       (Arith.nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One)))
   then [Stringa.Chara (true, false, true, false, true, true, false, false)]
   else (if Arith.equal_nat n
              (Arith.nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One)))
          then [Stringa.Chara
                  (false, true, true, false, true, true, false, false)]
          else (if Arith.equal_nat n
                     (Arith.nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One)))
                 then [Stringa.Chara
                         (true, true, true, false, true, true, false, false)]
                 else (if Arith.equal_nat n
                            (Arith.nat_of_num
                              (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One))))
                        then [Stringa.Chara
                                (false, false, false, true, true, true, false,
                                  false)]
                        else [Stringa.Chara
                                (true, false, false, true, true, true, false,
                                  false)])))))))));;

let rec string_of_nat
  n = (if Arith.less_nat n
            (Arith.nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))
        then string_of_digit n
        else string_of_nat
               (Arith.divide_nat n
                 (Arith.nat_of_num
                   (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))) @
               string_of_digit
                 (Arith.modulo_nat n
                   (Arith.nat_of_num
                     (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))));;

end;; (*struct Utils*)

module Nominal2_Base : sig
  type atom_sort = Sort of Stringa.char list * atom_sort list
  val equal_atom_sort : atom_sort HOL.equal
  val equal_atom_sorta : atom_sort -> atom_sort -> bool
  type atom = Atom of atom_sort * Arith.nat
  val equal_atom : atom -> atom -> bool
end = struct

type atom_sort = Sort of Stringa.char list * atom_sort list;;

let rec equal_atom_sort () =
  ({HOL.equal = equal_atom_sorta} : atom_sort HOL.equal)
and equal_atom_sorta
  (Sort (x1, x2)) (Sort (y1, y2)) =
    Lista.equal_lista Stringa.equal_char x1 y1 &&
      Lista.equal_lista (equal_atom_sort ()) x2 y2;;
let equal_atom_sort = equal_atom_sort ();;

type atom = Atom of atom_sort * Arith.nat;;

let rec equal_atom
  (Atom (x1, x2)) (Atom (y1, y2)) =
    equal_atom_sorta x1 y1 && Arith.equal_nat x2 y2;;

end;; (*struct Nominal2_Base*)

module Syntax : sig
  type bv = Abs_bv of Nominal2_Base.atom
  type b = B_int | B_bool | B_id of Stringa.char list | B_unit | B_pair of b * b
    | B_bitvec | B_var of bv | B_app of Stringa.char list * b
  type opp = Plus | LEq
  type x = Abs_x of Nominal2_Base.atom
  type bit = BitOne | BitZero
  type l = L_true | L_false | L_unit | L_num of Arith.int | L_bitvec of bit list
  type v = V_lit of l | V_var of x | V_pair of v * v |
    V_cons of Stringa.char list * Stringa.char list * v |
    V_consp of Stringa.char list * Stringa.char list * b * v
  type ce = CE_val of v | CE_fst of ce | CE_len of ce | CE_snd of ce |
    CE_op of opp * ce * ce | CE_concat of ce * ce
  type c = C_false | C_true | C_eq of ce * ce | C_imp of c * c | C_not of c |
    C_conj of c * c | C_disj of c * c
  type u = Abs_u of Nominal2_Base.atom
  type e = AE_val of v | AE_fst of v | AE_snd of v |
    AE_app of Stringa.char list * v | AE_appP of Stringa.char list * b * v |
    AE_len of v | AE_concat of v * v | AE_op of opp * v * v | AE_mvar of u |
    AE_split of v * v
  type tau = T_refined_type of x * b * c
  type s = AS_val of v | AS_let of x * e * s | AS_let2 of x * tau * s * s |
    AS_seq of s * s | AS_if of v * s * s | AS_while of s * s |
    AS_match of v * branch_list | AS_assign of u * v
  and branch_s = AS_branch of Stringa.char list * x * s
  and branch_list = AS_final of branch_s | AS_cons of branch_s * branch_list
  type fun_typ = AF_fun_typ of x * b * c * tau * s
  type fun_typ_q = AF_fun_typ_some of bv * fun_typ | AF_fun_typ_none of fun_typ
  type fun_def = AF_fundef of Stringa.char list * fun_typ_q
  type delta = DNil | DCons of (u * tau) * delta
  type gamma = GNil | GCons of (x * (b * c)) * gamma
  type type_def =
    AF_typedef of Stringa.char list * (Stringa.char list * tau) list
  val rep_x : x -> Nominal2_Base.atom
  val append_g : gamma -> gamma -> gamma
end = struct

type bv = Abs_bv of Nominal2_Base.atom;;

type b = B_int | B_bool | B_id of Stringa.char list | B_unit | B_pair of b * b |
  B_bitvec | B_var of bv | B_app of Stringa.char list * b;;

type opp = Plus | LEq;;

type x = Abs_x of Nominal2_Base.atom;;

type bit = BitOne | BitZero;;

type l = L_true | L_false | L_unit | L_num of Arith.int | L_bitvec of bit list;;

type v = V_lit of l | V_var of x | V_pair of v * v |
  V_cons of Stringa.char list * Stringa.char list * v |
  V_consp of Stringa.char list * Stringa.char list * b * v;;

type ce = CE_val of v | CE_fst of ce | CE_len of ce | CE_snd of ce |
  CE_op of opp * ce * ce | CE_concat of ce * ce;;

type c = C_false | C_true | C_eq of ce * ce | C_imp of c * c | C_not of c |
  C_conj of c * c | C_disj of c * c;;

type u = Abs_u of Nominal2_Base.atom;;

type e = AE_val of v | AE_fst of v | AE_snd of v |
  AE_app of Stringa.char list * v | AE_appP of Stringa.char list * b * v |
  AE_len of v | AE_concat of v * v | AE_op of opp * v * v | AE_mvar of u |
  AE_split of v * v;;

type tau = T_refined_type of x * b * c;;

type s = AS_val of v | AS_let of x * e * s | AS_let2 of x * tau * s * s |
  AS_seq of s * s | AS_if of v * s * s | AS_while of s * s |
  AS_match of v * branch_list | AS_assign of u * v
and branch_s = AS_branch of Stringa.char list * x * s
and branch_list = AS_final of branch_s | AS_cons of branch_s * branch_list;;

type fun_typ = AF_fun_typ of x * b * c * tau * s;;

type fun_typ_q = AF_fun_typ_some of bv * fun_typ | AF_fun_typ_none of fun_typ;;

type fun_def = AF_fundef of Stringa.char list * fun_typ_q;;

type delta = DNil | DCons of (u * tau) * delta;;

type gamma = GNil | GCons of (x * (b * c)) * gamma;;

type type_def =
  AF_typedef of Stringa.char list * (Stringa.char list * tau) list;;

let rec rep_x (Abs_x x) = x;;

let rec append_g x0 g = match x0, g with GNil, g -> g
                   | GCons (xbc, g1), g2 -> GCons (xbc, append_g g1 g2);;

end;; (*struct Syntax*)

module Show_Instances : sig
  val showsp_prod :
    (Arith.nat -> 'a -> Stringa.char list -> Stringa.char list) ->
      (Arith.nat -> 'b -> Stringa.char list -> Stringa.char list) ->
        Arith.nat -> 'a * 'b -> Stringa.char list -> Stringa.char list
  val shows_prec_prod :
    'a Show.show -> 'b Show.show ->
      Arith.nat -> 'a * 'b -> Stringa.char list -> Stringa.char list
  val shows_list_prod :
    'a Show.show -> 'b Show.show ->
      ('a * 'b) list -> Stringa.char list -> Stringa.char list
  val show_prod : 'a Show.show -> 'b Show.show -> ('a * 'b) Show.show
  val string_of_digit : Arith.nat -> Stringa.char list
  val showsp_nat :
    Arith.nat -> Arith.nat -> Stringa.char list -> Stringa.char list
  val showsp_int :
    Arith.nat -> Arith.int -> Stringa.char list -> Stringa.char list
  val shows_prec_nat :
    Arith.nat -> Arith.nat -> Stringa.char list -> Stringa.char list
end = struct

let rec showsp_prod
  s1 s2 p (x, y) =
    Fun.comp
      (Fun.comp
        (Fun.comp
          (Fun.comp
            (Show.shows_string
              [Stringa.Chara
                 (false, false, false, true, false, true, false, false)])
            (s1 Arith.one_nat x))
          (Show.shows_string
            [Stringa.Chara
               (false, false, true, true, false, true, false, false);
              Stringa.Chara
                (false, false, false, false, false, true, false, false)]))
        (s2 Arith.one_nat y))
      (Show.shows_string
        [Stringa.Chara (true, false, false, true, false, true, false, false)]);;

let rec shows_prec_prod _A _B
  = showsp_prod (Show.shows_prec _A) (Show.shows_prec _B);;

let rec shows_list_prod _A _B
  = Show.showsp_list (shows_prec_prod _A _B) Arith.Zero_nat;;

let rec show_prod _A _B =
  ({Show.shows_prec = shows_prec_prod _A _B;
     Show.shows_list = shows_list_prod _A _B}
    : ('a * 'b) Show.show);;

let rec string_of_digit
  n = (if Arith.equal_nat n Arith.Zero_nat
        then [Stringa.Chara
                (false, false, false, false, true, true, false, false)]
        else (if Arith.equal_nat n Arith.one_nat
               then [Stringa.Chara
                       (true, false, false, false, true, true, false, false)]
               else (if Arith.equal_nat n
                          (Arith.nat_of_num (Arith.Bit0 Arith.One))
                      then [Stringa.Chara
                              (false, true, false, false, true, true, false,
                                false)]
                      else (if Arith.equal_nat n
                                 (Arith.nat_of_num (Arith.Bit1 Arith.One))
                             then [Stringa.Chara
                                     (true, true, false, false, true, true,
                                       false, false)]
                             else (if Arith.equal_nat n
(Arith.nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One)))
                                    then [Stringa.Chara
    (false, false, true, false, true, true, false, false)]
                                    else (if Arith.equal_nat n
       (Arith.nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One)))
   then [Stringa.Chara (true, false, true, false, true, true, false, false)]
   else (if Arith.equal_nat n
              (Arith.nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One)))
          then [Stringa.Chara
                  (false, true, true, false, true, true, false, false)]
          else (if Arith.equal_nat n
                     (Arith.nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One)))
                 then [Stringa.Chara
                         (true, true, true, false, true, true, false, false)]
                 else (if Arith.equal_nat n
                            (Arith.nat_of_num
                              (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One))))
                        then [Stringa.Chara
                                (false, false, false, true, true, true, false,
                                  false)]
                        else [Stringa.Chara
                                (true, false, false, true, true, true, false,
                                  false)])))))))));;

let rec showsp_nat
  p n = (if Arith.less_nat n
              (Arith.nat_of_num
                (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))
          then Show.shows_string (string_of_digit n)
          else Fun.comp
                 (showsp_nat p
                   (Arith.divide_nat n
                     (Arith.nat_of_num
                       (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))))
                 (Show.shows_string
                   (string_of_digit
                     (Arith.modulo_nat n
                       (Arith.nat_of_num
                         (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One))))))));;

let rec showsp_int
  p i = (if Arith.less_int i Arith.Zero_int
          then Fun.comp
                 (Show.shows_string
                   [Stringa.Chara
                      (true, false, true, true, false, true, false, false)])
                 (showsp_nat p (Arith.nat (Arith.uminus_int i)))
          else showsp_nat p (Arith.nat i));;

let rec shows_prec_nat x = showsp_nat x;;

end;; (*struct Show_Instances*)

module ShowAST : sig
  val showsp_mut :
    Arith.nat -> Env.mut -> Stringa.char list -> Stringa.char list
  val shows_prec_mut :
    Arith.nat -> Env.mut -> Stringa.char list -> Stringa.char list
  val shows_list_mut : Env.mut list -> Stringa.char list -> Stringa.char list
  val show_mut : Env.mut Show.show
  val showsp_literal :
    Arith.nat -> string -> Stringa.char list -> Stringa.char list
  val showsp_id :
    Arith.nat -> SailAST.id -> Stringa.char list -> Stringa.char list
  val shows_prec_id :
    Arith.nat -> SailAST.id -> Stringa.char list -> Stringa.char list
  val shows_list_id : SailAST.id list -> Stringa.char list -> Stringa.char list
  val show_id : SailAST.id Show.show
  val showsp_kid :
    Arith.nat -> SailAST.kid -> Stringa.char list -> Stringa.char list
  val showsp_order :
    Arith.nat -> SailAST.order -> Stringa.char list -> Stringa.char list
  val showsp_integer :
    Arith.nat -> Z.t -> Stringa.char list -> Stringa.char list
  val showsp_nexp :
    Arith.nat -> SailAST.nexp -> Stringa.char list -> Stringa.char list
  val showsp_kind :
    Arith.nat -> SailAST.kind -> Stringa.char list -> Stringa.char list
  val showsp_kinded_id :
    Arith.nat -> SailAST.kinded_id -> Stringa.char list -> Stringa.char list
  val showsp_base_effect :
    Arith.nat -> SailAST.base_effect -> Stringa.char list -> Stringa.char list
  val showsp_effect :
    Arith.nat -> SailAST.effect -> Stringa.char list -> Stringa.char list
  val showsp_typ :
    Arith.nat -> SailAST.typ -> Stringa.char list -> Stringa.char list
  val showsp_typ_arg :
    Arith.nat -> SailAST.typ_arg -> Stringa.char list -> Stringa.char list
  val showsp_n_constraint :
    Arith.nat -> SailAST.n_constraint -> Stringa.char list -> Stringa.char list
  val shows_prec_typ :
    Arith.nat -> SailAST.typ -> Stringa.char list -> Stringa.char list
  val shows_list_typ :
    SailAST.typ list -> Stringa.char list -> Stringa.char list
  val show_typ : SailAST.typ Show.show
  val showsp_quant_item :
    Arith.nat -> SailAST.quant_item -> Stringa.char list -> Stringa.char list
  val showsp_typquant :
    Arith.nat -> SailAST.typquant -> Stringa.char list -> Stringa.char list
  val shows_prec_typquant :
    Arith.nat -> SailAST.typquant -> Stringa.char list -> Stringa.char list
  val shows_list_typquant :
    SailAST.typquant list -> Stringa.char list -> Stringa.char list
  val show_typquant : SailAST.typquant Show.show
  val showsp_type_union :
    Arith.nat -> SailAST.type_union -> Stringa.char list -> Stringa.char list
  val shows_prec_type_union :
    Arith.nat -> SailAST.type_union -> Stringa.char list -> Stringa.char list
  val shows_list_type_union :
    SailAST.type_union list -> Stringa.char list -> Stringa.char list
  val show_type_union : SailAST.type_union Show.show
  val shows_prec_typ_arg :
    Arith.nat -> SailAST.typ_arg -> Stringa.char list -> Stringa.char list
  val shows_prec_kind :
    Arith.nat -> SailAST.kind -> Stringa.char list -> Stringa.char list
  val shows_prec_kid :
    Arith.nat -> SailAST.kid -> Stringa.char list -> Stringa.char list
  val show_env : unit Env.env_ext -> Stringa.char list
  val show_tannot : unit Env.tannot_ext option -> Stringa.char list
  val shows_prec_n_constraint :
    Arith.nat -> SailAST.n_constraint -> Stringa.char list -> Stringa.char list
end = struct

let rec showsp_mut
  p x1 = match p, x1 with
    p, Env.Immutable ->
      Show.shows_string
        [Stringa.Chara (true, false, false, true, false, false, true, false);
          Stringa.Chara (true, false, true, true, false, true, true, false);
          Stringa.Chara (true, false, true, true, false, true, true, false);
          Stringa.Chara (true, false, true, false, true, true, true, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, true, false, false, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false);
          Stringa.Chara (true, false, true, false, false, true, true, false)]
    | p, Env.Mutable ->
        Show.shows_string
          [Stringa.Chara (true, false, true, true, false, false, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (false, true, false, false, false, true, true, false);
            Stringa.Chara (false, false, true, true, false, true, true, false);
            Stringa.Chara
              (true, false, true, false, false, true, true, false)];;

let rec shows_prec_mut x = showsp_mut x;;

let rec shows_list_mut x = Show.showsp_list shows_prec_mut Arith.Zero_nat x;;

let show_mut =
  ({Show.shows_prec = shows_prec_mut; Show.shows_list = shows_list_mut} :
    Env.mut Show.show);;

let rec showsp_literal p n = Show.shows_string (Stringa.explode n);;

let rec showsp_id
  p x1 = match p, x1 with
    p, SailAST.Operator x ->
      Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp (Show.shows_pl p)
              (Show.shows_string
                [Stringa.Chara
                   (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (false, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, true, false, false, true, true, true, false)]))
            Show.shows_space)
          (showsp_literal Arith.one_nat x))
        (Show.shows_pr p)
    | p, SailAST.Id x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_literal Arith.one_nat x))
          (Show.shows_pr p);;

let rec shows_prec_id x = showsp_id x;;

let rec shows_list_id x = Show.showsp_list shows_prec_id Arith.Zero_nat x;;

let show_id =
  ({Show.shows_prec = shows_prec_id; Show.shows_list = shows_list_id} :
    SailAST.id Show.show);;

let rec showsp_kid
  p (SailAST.Var x) =
    Fun.comp
      (Fun.comp
        (Fun.comp
          (Fun.comp (Show.shows_pl p)
            (Show.shows_string
              [Stringa.Chara
                 (false, true, true, false, true, true, true, false);
                Stringa.Chara
                  (true, false, false, false, false, true, true, false);
                Stringa.Chara
                  (false, true, false, false, true, true, true, false)]))
          Show.shows_space)
        (showsp_literal Arith.one_nat x))
      (Show.shows_pr p);;

let rec showsp_order
  p x1 = match p, x1 with
    p, SailAST.Ord_dec ->
      Show.shows_string
        [Stringa.Chara (true, true, true, true, false, false, true, false);
          Stringa.Chara (false, true, false, false, true, true, true, false);
          Stringa.Chara (false, false, true, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, false, true, false, false, true, true, false);
          Stringa.Chara (true, false, true, false, false, true, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false)]
    | p, SailAST.Ord_inc ->
        Show.shows_string
          [Stringa.Chara (true, true, true, true, false, false, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, false, true, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, false, false, false, true, true, false)]
    | p, SailAST.Ord_var x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, true, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_kid Arith.one_nat x))
          (Show.shows_pr p);;

let rec showsp_integer
  p n = Show_Instances.showsp_int p (Arith.int_of_integer n);;

let rec showsp_nexp
  p x1 = match p, x1 with
    p, SailAST.Nexp_neg x ->
      Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp (Show.shows_pl p)
              (Show.shows_string
                [Stringa.Chara
                   (false, true, true, true, false, false, true, false);
                  Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (false, false, false, true, true, true, true, false);
                  Stringa.Chara
                    (false, false, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, true, false, true, false);
                  Stringa.Chara
                    (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, false, false, true, true, false)]))
            Show.shows_space)
          (showsp_nexp Arith.one_nat x))
        (Show.shows_pr p)
    | p, SailAST.Nexp_exp x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_nexp Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Nexp_minus (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, false, false, true, true, true, false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.Nexp_sum (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, true, false, true, true, false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.Nexp_times (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, false, false, true, true, true, false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.Nexp_app (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_id Arith.one_nat x))
              Show.shows_space)
            (Show.showsp_list showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.Nexp_constant x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, true, false, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (true, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_integer Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Nexp_var x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, true, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_kid Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Nexp_id x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_id Arith.one_nat x))
          (Show.shows_pr p);;

let rec showsp_kind
  p x1 = match p, x1 with
    p, SailAST.K_bool ->
      Show.shows_string
        [Stringa.Chara (true, true, false, true, false, false, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, true, false, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false)]
    | p, SailAST.K_order ->
        Show.shows_string
          [Stringa.Chara (true, true, false, true, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, true, true, true, false, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false)]
    | p, SailAST.K_int ->
        Show.shows_string
          [Stringa.Chara (true, true, false, true, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, false, true, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false)]
    | p, SailAST.K_type ->
        Show.shows_string
          [Stringa.Chara (true, true, false, true, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false);
            Stringa.Chara (true, false, false, true, true, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara
              (true, false, true, false, false, true, true, false)];;

let rec showsp_kinded_id
  p (SailAST.KOpt_kind (x, y)) =
    Fun.comp
      (Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, true, false, true, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, true, false, true, false, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_kind Arith.one_nat x))
          Show.shows_space)
        (showsp_kid Arith.one_nat y))
      (Show.shows_pr p);;

let rec showsp_base_effect
  p x1 = match p, x1 with
    p, SailAST.BE_config ->
      Show.shows_string
        [Stringa.Chara (false, true, false, false, false, false, true, false);
          Stringa.Chara (true, false, true, false, false, false, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, false, false, true, true, false);
          Stringa.Chara (true, false, false, true, false, true, true, false);
          Stringa.Chara (true, true, true, false, false, true, true, false)]
    | p, SailAST.BE_escape ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, false, false, true, true, true, false);
            Stringa.Chara (true, true, false, false, false, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false)]
    | p, SailAST.BE_nondet ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, true, true, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false)]
    | p, SailAST.BE_unspec ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, false, false, true, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, false, false, false, true, true, false)]
    | p, SailAST.BE_undef ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, true, true, false, false, true, true, false)]
    | p, SailAST.BE_depend ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false)]
    | p, SailAST.BE_barr ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, false, false, false, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false)]
    | p, SailAST.BE_wmvt ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, true, true, false, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (false, true, true, false, true, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false)]
    | p, SailAST.BE_wmv ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, true, true, false, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (false, true, true, false, true, true, true, false)]
    | p, SailAST.BE_exmem ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, false, false, true, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false)]
    | p, SailAST.BE_eamem ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false)]
    | p, SailAST.BE_wmem ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, true, true, false, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false)]
    | p, SailAST.BE_rmemt ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false)]
    | p, SailAST.BE_rmem ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, false, true, true, false, true, true, false)]
    | p, SailAST.BE_wreg ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, true, true, false, true, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, true, false, false, true, true, false)]
    | p, SailAST.BE_rreg ->
        Show.shows_string
          [Stringa.Chara (false, true, false, false, false, false, true, false);
            Stringa.Chara (true, false, true, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, true, false, false, true, true, false)];;

let rec showsp_effect
  p (SailAST.Effect_set x) =
    Fun.comp
      (Fun.comp
        (Fun.comp
          (Fun.comp (Show.shows_pl p)
            (Show.shows_string
              [Stringa.Chara
                 (true, false, true, false, false, false, true, false);
                Stringa.Chara
                  (false, true, true, false, false, true, true, false);
                Stringa.Chara
                  (false, true, true, false, false, true, true, false);
                Stringa.Chara
                  (true, false, true, false, false, true, true, false);
                Stringa.Chara
                  (true, true, false, false, false, true, true, false);
                Stringa.Chara
                  (false, false, true, false, true, true, true, false);
                Stringa.Chara
                  (true, true, true, true, true, false, true, false);
                Stringa.Chara
                  (true, true, false, false, true, true, true, false);
                Stringa.Chara
                  (true, false, true, false, false, true, true, false);
                Stringa.Chara
                  (false, false, true, false, true, true, true, false)]))
          Show.shows_space)
        (Show.showsp_list showsp_base_effect Arith.one_nat x))
      (Show.shows_pr p);;

let rec showsp_typ
  p x1 = match p, x1 with
    p, SailAST.Typ_exist (x, y, z) ->
      Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp
                    (Fun.comp (Show.shows_pl p)
                      (Show.shows_string
                        [Stringa.Chara
                           (false, false, true, false, true, false, true,
                             false);
                          Stringa.Chara
                            (true, false, false, true, true, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, false, true, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, false, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false)]))
                    Show.shows_space)
                  (Show.showsp_list showsp_kinded_id Arith.one_nat x))
                Show.shows_space)
              (showsp_n_constraint Arith.one_nat y))
            Show.shows_space)
          (showsp_typ Arith.one_nat z))
        (Show.shows_pr p)
    | p, SailAST.Typ_app (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, false, true, false, true, false, true, false);
                        Stringa.Chara
                          (true, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_id Arith.one_nat x))
              Show.shows_space)
            (Show.showsp_list showsp_typ_arg Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.Typ_tup x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, false, true, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false)]))
              Show.shows_space)
            (Show.showsp_list showsp_typ Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Typ_bidir (x, y, z) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp
                    (Fun.comp
                      (Fun.comp (Show.shows_pl p)
                        (Show.shows_string
                          [Stringa.Chara
                             (false, false, true, false, true, false, true,
                               false);
                            Stringa.Chara
                              (true, false, false, true, true, true, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, true, true,
                                false);
                            Stringa.Chara
                              (false, false, true, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, false, false, true, true, true,
                                false)]))
                      Show.shows_space)
                    (showsp_typ Arith.one_nat x))
                  Show.shows_space)
                (showsp_typ Arith.one_nat y))
              Show.shows_space)
            (showsp_effect Arith.one_nat z))
          (Show.shows_pr p)
    | p, SailAST.Typ_fn (x, y, z) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp
                    (Fun.comp
                      (Fun.comp (Show.shows_pl p)
                        (Show.shows_string
                          [Stringa.Chara
                             (false, false, true, false, true, false, true,
                               false);
                            Stringa.Chara
                              (true, false, false, true, true, true, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, true, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, true, true, false, true, true,
                                false)]))
                      Show.shows_space)
                    (Show.showsp_list showsp_typ Arith.one_nat x))
                  Show.shows_space)
                (showsp_typ Arith.one_nat y))
              Show.shows_space)
            (showsp_effect Arith.one_nat z))
          (Show.shows_pr p)
    | p, SailAST.Typ_var x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, false, true, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, true, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_kid Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Typ_id x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, false, true, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_id Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.Typ_internal_unknown ->
        Show.shows_string
          [Stringa.Chara (false, false, true, false, true, false, true, false);
            Stringa.Chara (true, false, false, true, true, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, false, true, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, false, false, false, false, true, true, false);
            Stringa.Chara (false, false, true, true, false, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, false, true, false, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, true, true, false, true, true, false);
            Stringa.Chara (true, true, true, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false)]
and showsp_typ_arg
  p x1 = match p, x1 with
    p, SailAST.A_bool x ->
      Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp (Show.shows_pl p)
              (Show.shows_string
                [Stringa.Chara
                   (true, false, false, false, false, false, true, false);
                  Stringa.Chara
                    (true, true, true, true, true, false, true, false);
                  Stringa.Chara
                    (false, true, false, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, true, false, true, true, false)]))
            Show.shows_space)
          (showsp_n_constraint Arith.one_nat x))
        (Show.shows_pr p)
    | p, SailAST.A_order x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, false, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_order Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.A_typ x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, false, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_typ Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.A_nexp x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, false, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_nexp Arith.one_nat x))
          (Show.shows_pr p)
and showsp_n_constraint
  p x1 = match p, x1 with
    p, SailAST.NC_false ->
      Show.shows_string
        [Stringa.Chara (false, true, true, true, false, false, true, false);
          Stringa.Chara (true, true, false, false, false, false, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, true, true, false, false, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, true, true, true, false);
          Stringa.Chara (true, false, true, false, false, true, true, false)]
    | p, SailAST.NC_true ->
        Show.shows_string
          [Stringa.Chara (false, true, true, true, false, false, true, false);
            Stringa.Chara (true, true, false, false, false, false, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, false, true, false, true, true, true, false);
            Stringa.Chara (false, true, false, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false)]
    | p, SailAST.NC_var x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, true, true, true, false, false, true, false);
                    Stringa.Chara
                      (true, true, false, false, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, true, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_kid Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.NC_app (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_id Arith.one_nat x))
              Show.shows_space)
            (Show.showsp_list showsp_typ_arg Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_and (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_n_constraint Arith.one_nat x))
              Show.shows_space)
            (showsp_n_constraint Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_or (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, true, false, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_n_constraint Arith.one_nat x))
              Show.shows_space)
            (showsp_n_constraint Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_set (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_kid Arith.one_nat x))
              Show.shows_space)
            (Show.showsp_list showsp_integer Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_not_equal (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_bounded_lt (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_bounded_le (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_bounded_gt (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_bounded_ge (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p)
    | p, SailAST.NC_equal (x, y) ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp
                (Fun.comp
                  (Fun.comp (Show.shows_pl p)
                    (Show.shows_string
                      [Stringa.Chara
                         (false, true, true, true, false, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, false, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true,
                            false)]))
                  Show.shows_space)
                (showsp_nexp Arith.one_nat x))
              Show.shows_space)
            (showsp_nexp Arith.one_nat y))
          (Show.shows_pr p);;

let rec shows_prec_typ x = showsp_typ x;;

let rec shows_list_typ x = Show.showsp_list shows_prec_typ Arith.Zero_nat x;;

let show_typ =
  ({Show.shows_prec = shows_prec_typ; Show.shows_list = shows_list_typ} :
    SailAST.typ Show.show);;

let rec showsp_quant_item
  p x1 = match p, x1 with
    p, SailAST.QI_constant x ->
      Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp (Show.shows_pl p)
              (Show.shows_string
                [Stringa.Chara
                   (true, false, false, false, true, false, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, false, true, false);
                  Stringa.Chara
                    (true, true, true, true, true, false, true, false);
                  Stringa.Chara
                    (true, true, false, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, true, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)]))
            Show.shows_space)
          (Show.showsp_list showsp_kinded_id Arith.one_nat x))
        (Show.shows_pr p)
    | p, SailAST.QI_constraint x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, true, false, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (true, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (false, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, false, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, true, true, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false)]))
              Show.shows_space)
            (showsp_n_constraint Arith.one_nat x))
          (Show.shows_pr p)
    | p, SailAST.QI_id x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (true, false, false, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_kinded_id Arith.one_nat x))
          (Show.shows_pr p);;

let rec showsp_typquant
  p x1 = match p, x1 with
    p, SailAST.TypQ_no_forall ->
      Show.shows_string
        [Stringa.Chara (false, false, true, false, true, false, true, false);
          Stringa.Chara (true, false, false, true, true, true, true, false);
          Stringa.Chara (false, false, false, false, true, true, true, false);
          Stringa.Chara (true, false, false, false, true, false, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, true, true, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, false, false, true, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false)]
    | p, SailAST.TypQ_tq x ->
        Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, false, true, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, true, false, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, false, true, true, true, false)]))
              Show.shows_space)
            (Show.showsp_list showsp_quant_item Arith.one_nat x))
          (Show.shows_pr p);;

let rec shows_prec_typquant x = showsp_typquant x;;

let rec shows_list_typquant
  x = Show.showsp_list shows_prec_typquant Arith.Zero_nat x;;

let show_typquant =
  ({Show.shows_prec = shows_prec_typquant;
     Show.shows_list = shows_list_typquant}
    : SailAST.typquant Show.show);;

let rec showsp_type_union
  p (SailAST.Tu_ty_id (x, y)) =
    Fun.comp
      (Fun.comp
        (Fun.comp
          (Fun.comp
            (Fun.comp
              (Fun.comp (Show.shows_pl p)
                (Show.shows_string
                  [Stringa.Chara
                     (false, false, true, false, true, false, true, false);
                    Stringa.Chara
                      (true, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (false, false, true, false, false, true, true, false)]))
              Show.shows_space)
            (showsp_typ Arith.one_nat x))
          Show.shows_space)
        (showsp_id Arith.one_nat y))
      (Show.shows_pr p);;

let rec shows_prec_type_union x = showsp_type_union x;;

let rec shows_list_type_union
  x = Show.showsp_list shows_prec_type_union Arith.Zero_nat x;;

let show_type_union =
  ({Show.shows_prec = shows_prec_type_union;
     Show.shows_list = shows_list_type_union}
    : SailAST.type_union Show.show);;

let rec shows_prec_typ_arg x = showsp_typ_arg x;;

let rec shows_prec_kind x = showsp_kind x;;

let rec shows_prec_kid x = showsp_kid x;;

let rec show_env
  env = [Stringa.Chara (false, false, true, true, false, false, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, true, true, true, false);
          Stringa.Chara (false, true, false, true, true, true, false, false);
          Stringa.Chara
            (false, false, false, false, false, true, false, false)] @
          Lista.maps
            (fun (i, t) ->
              shows_prec_id Arith.Zero_nat i [] @
                [Stringa.Chara
                   (false, true, false, true, true, true, false, false);
                  Stringa.Chara
                    (false, true, false, true, true, true, false, false)] @
                  Show_Instances.shows_prec_prod show_mut show_typ
                    Arith.Zero_nat t [] @
                    [Stringa.Chara
                       (false, false, false, false, false, true, false, false)])
            (Env.locals env) @
            [Stringa.Chara
               (false, true, false, true, false, false, false, false)] @
              [Stringa.Chara
                 (false, false, true, false, true, false, true, false);
                Stringa.Chara
                  (true, false, false, true, true, true, true, false);
                Stringa.Chara
                  (false, false, false, false, true, true, true, false);
                Stringa.Chara
                  (false, true, true, false, true, true, true, false);
                Stringa.Chara
                  (true, false, false, false, false, true, true, false);
                Stringa.Chara
                  (false, true, false, false, true, true, true, false);
                Stringa.Chara
                  (true, true, false, false, true, true, true, false);
                Stringa.Chara
                  (false, true, false, true, true, true, false, false);
                Stringa.Chara
                  (false, false, false, false, false, true, false, false)] @
                Lista.maps
                  (fun (i, t) ->
                    shows_prec_kid Arith.Zero_nat i [] @
                      [Stringa.Chara
                         (false, true, false, true, true, true, false, false);
                        Stringa.Chara
                          (false, true, false, true, true, true, false,
                            false)] @
                        shows_prec_kind Arith.Zero_nat t [] @
                          [Stringa.Chara
                             (false, false, false, false, false, true, false,
                               false)])
                  (Env.typ_vars env) @
                  [Stringa.Chara
                     (false, true, false, true, false, false, false, false)] @
                    [Stringa.Chara
                       (false, true, true, false, true, false, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, false, true, false, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, true, false, true, true, true, false, false);
                      Stringa.Chara
                        (false, false, false, false, false, true, false,
                          false)] @
                      Lista.maps
                        (fun (i, t) ->
                          shows_prec_id Arith.Zero_nat i [] @
                            [Stringa.Chara
                               (false, true, false, true, true, true, false,
                                 false);
                              Stringa.Chara
                                (false, true, false, true, true, true, false,
                                  false)] @
                              Show_Instances.shows_prec_prod show_typquant
                                show_typ Arith.Zero_nat t [] @
                                [Stringa.Chara
                                   (false, false, false, false, false, true,
                                     false, false)])
                        (Env.top_val_specs env) @
                        [Stringa.Chara
                           (false, true, false, true, false, false, false,
                             false)] @
                          [Stringa.Chara
                             (false, true, true, false, true, false, true,
                               false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, true, true, false, true, true,
                                false);
                            Stringa.Chara
                              (false, false, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, true, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (false, true, false, true, true, true, false,
                                false);
                            Stringa.Chara
                              (false, false, false, false, false, true, false,
                                false)] @
                            Lista.maps
                              (fun (i, t) ->
                                shows_prec_id Arith.Zero_nat i [] @
                                  [Stringa.Chara
                                     (false, true, false, true, true, true,
                                       false, false);
                                    Stringa.Chara
                                      (false, true, false, true, true, true,
false, false)] @
                                    Show_Instances.shows_prec_prod show_typquant
                                      (Show.show_list show_type_union)
                                      Arith.Zero_nat t [] @
                                      [Stringa.Chara
 (false, false, false, false, false, true, false, false)])
                              (Env.variants env) @
                              [Stringa.Chara
                                 (false, true, false, true, false, false, false,
                                   false)] @
                                [Stringa.Chara
                                   (false, true, false, false, true, false,
                                     true, false);
                                  Stringa.Chara
                                    (true, false, true, false, false, true,
                                      true, false);
                                  Stringa.Chara
                                    (true, true, false, false, false, true,
                                      true, false);
                                  Stringa.Chara
                                    (true, true, true, true, false, true, true,
                                      false);
                                  Stringa.Chara
                                    (false, true, false, false, true, true,
                                      true, false);
                                  Stringa.Chara
                                    (false, false, true, false, false, true,
                                      true, false);
                                  Stringa.Chara
                                    (true, true, false, false, true, true, true,
                                      false);
                                  Stringa.Chara
                                    (false, true, false, true, true, true,
                                      false, false);
                                  Stringa.Chara
                                    (false, false, false, false, false, true,
                                      false, false)] @
                                  Lista.maps
                                    (fun (i, t) ->
                                      shows_prec_id Arith.Zero_nat i [] @
[Stringa.Chara (false, true, false, true, true, true, false, false);
  Stringa.Chara (false, true, false, true, true, true, false, false)] @
  Show_Instances.shows_prec_prod show_typquant
    (Show.show_list (Show_Instances.show_prod show_id show_typ)) Arith.Zero_nat
    t [] @
    [Stringa.Chara (false, false, false, false, false, true, false, false)])
                                    (Env.records env) @
                                    [Stringa.Chara
                                       (false, true, false, true, false, false,
 false, false)] @
                                      [Stringa.Chara
 (false, false, true, false, true, false, true, false);
Stringa.Chara (true, false, false, true, true, true, true, false);
Stringa.Chara (false, false, false, false, true, true, true, false);
Stringa.Chara (true, true, false, false, true, true, true, false);
Stringa.Chara (true, false, false, true, true, true, true, false);
Stringa.Chara (false, true, true, true, false, true, true, false);
Stringa.Chara (false, true, false, true, true, true, false, false);
Stringa.Chara (false, false, false, false, false, true, false, false)] @
Lista.maps
  (fun (i, (tq, ta)) ->
    shows_prec_id Arith.Zero_nat i [] @
      [Stringa.Chara (false, true, false, true, true, true, false, false);
        Stringa.Chara (false, true, false, true, true, true, false, false)] @
        shows_prec_typquant Arith.Zero_nat tq [] @
          shows_prec_typ_arg Arith.Zero_nat ta [] @
            [Stringa.Chara
               (false, false, false, false, false, true, false, false)])
  (Env.typ_synonyms env);;

let rec show_tannot
  = function
    None ->
      [Stringa.Chara (false, false, true, false, true, true, true, false);
        Stringa.Chara (true, false, false, false, false, true, true, false);
        Stringa.Chara (false, true, true, true, false, true, true, false);
        Stringa.Chara (false, true, true, true, false, true, true, false);
        Stringa.Chara (true, true, true, true, false, true, true, false);
        Stringa.Chara (false, false, true, false, true, true, true, false);
        Stringa.Chara (false, false, false, false, false, true, false, false);
        Stringa.Chara (true, false, true, true, true, true, false, false);
        Stringa.Chara (false, false, false, false, false, true, false, false);
        Stringa.Chara (false, false, false, true, false, true, false, false);
        Stringa.Chara (false, true, true, true, false, false, true, false);
        Stringa.Chara (true, true, true, true, false, true, true, false);
        Stringa.Chara (false, true, true, true, false, true, true, false);
        Stringa.Chara (true, false, true, false, false, true, true, false);
        Stringa.Chara (true, false, false, true, false, true, false, false)]
    | Some t ->
        [Stringa.Chara (true, false, false, true, false, false, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, true, true, true, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (false, true, false, true, true, true, false, false);
          Stringa.Chara
            (false, false, false, false, false, true, false, false)] @
          (match Env.tannot_instantiations t
            with None ->
              [Stringa.Chara
                 (false, false, false, true, false, true, false, false);
                Stringa.Chara
                  (false, true, true, true, false, true, true, false);
                Stringa.Chara
                  (true, true, true, true, false, true, true, false);
                Stringa.Chara
                  (false, true, true, true, false, true, true, false);
                Stringa.Chara
                  (true, false, true, false, false, true, true, false);
                Stringa.Chara
                  (true, false, false, true, false, true, false, false)]
            | Some a ->
              Lista.maps
                (fun (i, ta) ->
                  shows_prec_kid Arith.Zero_nat i [] @
                    [Stringa.Chara
                       (false, false, false, false, false, true, false, false);
                      Stringa.Chara
                        (true, false, true, true, true, true, false, false);
                      Stringa.Chara
                        (false, false, false, false, false, true, false,
                          false)] @
                      shows_prec_typ_arg Arith.Zero_nat ta [] @
                        [Stringa.Chara
                           (false, false, false, false, false, true, false,
                             false)])
                a) @
            [Stringa.Chara
               (false, true, false, true, false, false, false, false)] @
              [Stringa.Chara
                 (false, false, true, false, true, false, true, false);
                Stringa.Chara
                  (true, false, false, true, true, true, true, false);
                Stringa.Chara
                  (false, false, false, false, true, true, true, false);
                Stringa.Chara
                  (false, true, false, true, true, true, false, false);
                Stringa.Chara
                  (false, false, false, false, false, true, false, false)] @
                shows_prec_typ Arith.Zero_nat (Env.tannot_typ t) [];;

let rec shows_prec_n_constraint x = showsp_n_constraint x;;

end;; (*struct ShowAST*)

module AstUtils : sig
  val int_typ : SailAST.typ
  val unit_typ : SailAST.typ
  val collect_pat : ('a SailAST.pat -> 'b list) -> 'a SailAST.pat -> 'b list
  val collect_e :
    ('a SailAST.pat -> 'b list) ->
      ('a SailAST.exp -> 'b list) -> 'a SailAST.exp -> 'b list
  val collect_pexp :
    ('a SailAST.pat -> 'b list) ->
      ('a SailAST.exp -> 'b list) -> 'a SailAST.pexp -> 'b list
  val bool_all_typ : SailAST.typ
end = struct

let int_typ : SailAST.typ = SailAST.Typ_id (SailAST.Id "int");;

let unit_typ : SailAST.typ = SailAST.Typ_id (SailAST.Id "unit");;

let rec collect_pat
  f x1 = match f, x1 with
    f, SailAST.P_or (t, p1, p2) ->
      f (SailAST.P_or (t, p1, p2)) @ collect_pat f p1 @ collect_pat f p2
    | f, SailAST.P_not (t, p) -> f (SailAST.P_not (t, p)) @ collect_pat f p
    | f, SailAST.P_tup (t, pats) ->
        f (SailAST.P_tup (t, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_as (t, pat, i) ->
        f (SailAST.P_as (t, pat, i)) @ collect_pat f pat
    | f, SailAST.P_typ (t, typ, pat) ->
        f (SailAST.P_typ (t, typ, pat)) @ collect_pat f pat
    | f, SailAST.P_app (t, ff, pats) ->
        f (SailAST.P_app (t, ff, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_vector (t, pats) ->
        f (SailAST.P_vector (t, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_vector_concat (t, pats) ->
        f (SailAST.P_vector_concat (t, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_list (t, pats) ->
        f (SailAST.P_list (t, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_cons (t, p1, p2) ->
        f (SailAST.P_cons (t, p1, p2)) @ collect_pat f p1 @ collect_pat f p2
    | f, SailAST.P_string_append (t, pats) ->
        f (SailAST.P_string_append (t, pats)) @ Lista.maps (collect_pat f) pats
    | f, SailAST.P_lit (v, va) -> f (SailAST.P_lit (v, va))
    | f, SailAST.P_wild v -> f (SailAST.P_wild v)
    | f, SailAST.P_id (v, va) -> f (SailAST.P_id (v, va))
    | f, SailAST.P_var (v, va, vb) -> f (SailAST.P_var (v, va, vb));;

let rec collect_e
  f1 f2 x2 = match f1, f2, x2 with
    f1, f2, SailAST.E_block (t, es) ->
      f2 (SailAST.E_block (t, es)) @ Lista.maps (collect_e f1 f2) es
    | f1, f2, SailAST.E_if (t, e1, e2, e3) ->
        f2 (SailAST.E_if (t, e1, e2, e2)) @
          collect_e f1 f2 e1 @ collect_e f1 f2 e2 @ collect_e f1 f2 e3
    | f1, f2, SailAST.E_case (t, e1, pexps) ->
        f2 (SailAST.E_case (t, e1, pexps)) @
          Lista.maps (collect_pexp f1 f2) pexps
    | f1, f2, SailAST.E_id (v, va) -> f2 (SailAST.E_id (v, va))
    | f1, f2, SailAST.E_lit (v, va) -> f2 (SailAST.E_lit (v, va))
    | f1, f2, SailAST.E_cast (v, va, vb) -> f2 (SailAST.E_cast (v, va, vb))
    | f1, f2, SailAST.E_app (v, va, vb) -> f2 (SailAST.E_app (v, va, vb))
    | f1, f2, SailAST.E_app_infix (v, va, vb, vc) ->
        f2 (SailAST.E_app_infix (v, va, vb, vc))
    | f1, f2, SailAST.E_tuple (v, va) -> f2 (SailAST.E_tuple (v, va))
    | f1, f2, SailAST.E_loop (v, va, vb, vc, vd) ->
        f2 (SailAST.E_loop (v, va, vb, vc, vd))
    | f1, f2, SailAST.E_for (v, va, vb, vc, vd, ve, vf) ->
        f2 (SailAST.E_for (v, va, vb, vc, vd, ve, vf))
    | f1, f2, SailAST.E_vector (v, va) -> f2 (SailAST.E_vector (v, va))
    | f1, f2, SailAST.E_vector_access (v, va, vb) ->
        f2 (SailAST.E_vector_access (v, va, vb))
    | f1, f2, SailAST.E_vector_subrange (v, va, vb, vc) ->
        f2 (SailAST.E_vector_subrange (v, va, vb, vc))
    | f1, f2, SailAST.E_vector_update (v, va, vb, vc) ->
        f2 (SailAST.E_vector_update (v, va, vb, vc))
    | f1, f2, SailAST.E_vector_update_subrange (v, va, vb, vc, vd) ->
        f2 (SailAST.E_vector_update_subrange (v, va, vb, vc, vd))
    | f1, f2, SailAST.E_vector_append (v, va, vb) ->
        f2 (SailAST.E_vector_append (v, va, vb))
    | f1, f2, SailAST.E_list (v, va) -> f2 (SailAST.E_list (v, va))
    | f1, f2, SailAST.E_cons (v, va, vb) -> f2 (SailAST.E_cons (v, va, vb))
    | f1, f2, SailAST.E_record (v, va) -> f2 (SailAST.E_record (v, va))
    | f1, f2, SailAST.E_record_update (v, va, vb) ->
        f2 (SailAST.E_record_update (v, va, vb))
    | f1, f2, SailAST.E_field (v, va, vb) -> f2 (SailAST.E_field (v, va, vb))
    | f1, f2, SailAST.E_let (v, va, vb) -> f2 (SailAST.E_let (v, va, vb))
    | f1, f2, SailAST.E_assign (v, va, vb) -> f2 (SailAST.E_assign (v, va, vb))
    | f1, f2, SailAST.E_sizeof (v, va) -> f2 (SailAST.E_sizeof (v, va))
    | f1, f2, SailAST.E_return (v, va) -> f2 (SailAST.E_return (v, va))
    | f1, f2, SailAST.E_exit (v, va) -> f2 (SailAST.E_exit (v, va))
    | f1, f2, SailAST.E_ref (v, va) -> f2 (SailAST.E_ref (v, va))
    | f1, f2, SailAST.E_throw (v, va) -> f2 (SailAST.E_throw (v, va))
    | f1, f2, SailAST.E_try (v, va, vb) -> f2 (SailAST.E_try (v, va, vb))
    | f1, f2, SailAST.E_assert (v, va, vb) -> f2 (SailAST.E_assert (v, va, vb))
    | f1, f2, SailAST.E_var (v, va, vb, vc) ->
        f2 (SailAST.E_var (v, va, vb, vc))
    | f1, f2, SailAST.E_internal_plet (v, va, vb, vc) ->
        f2 (SailAST.E_internal_plet (v, va, vb, vc))
    | f1, f2, SailAST.E_internal_return (v, va) ->
        f2 (SailAST.E_internal_return (v, va))
    | f1, f2, SailAST.E_internal_value (v, va) ->
        f2 (SailAST.E_internal_value (v, va))
    | f1, f2, SailAST.E_constraint (v, va) -> f2 (SailAST.E_constraint (v, va))
and collect_pexp
  f1 f2 (SailAST.Pat_exp (t, p, e)) = collect_pat f1 p @ collect_e f1 f2 e;;

let bool_all_typ : SailAST.typ = SailAST.Typ_id (SailAST.Id "bool");;

end;; (*struct AstUtils*)

module CodeGenPrelude : sig
  val eq_atom_x : Nominal2_Base.atom -> Nominal2_Base.atom -> bool
  val eq_x : Syntax.x -> Syntax.x -> bool
  val equal_xa : Syntax.x -> Syntax.x -> bool
  val equal_x : Syntax.x HOL.equal
end = struct

let rec eq_atom_x x y = Nominal2_Base.equal_atom x y;;

let rec eq_x x xb = eq_atom_x (Syntax.rep_x x) (Syntax.rep_x xb);;

let rec equal_xa x y = eq_x x y;;

let equal_x = ({HOL.equal = equal_xa} : Syntax.x HOL.equal);;

end;; (*struct CodeGenPrelude*)

module Predicate : sig
  type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  and 'a pred = Seq of (unit -> 'a seq)
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val eval : 'a HOL.equal -> 'a pred -> 'a -> bool
  val member : 'a HOL.equal -> 'a seq -> 'a -> bool
  val holds : unit pred -> bool
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

let rec eval _A (Seq f) = member _A (f ())
and member _A xa0 x = match xa0, x with Empty, x -> false
                | Insert (y, p), x -> HOL.eq _A x y || eval _A p x
                | Join (p, xq), x -> eval _A p x || member _A xq x;;

let rec holds p = eval Product_Type.equal_unit p ();;

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

module SailToMs : sig
  type lctx = L_hole | L_continue | L_val of Syntax.v |
    L_let of Syntax.x * Syntax.e * lctx | L_if1 of Syntax.v * lctx * Syntax.s |
    L_if2 of Syntax.v * Syntax.s * lctx | L_if3 of Syntax.v * lctx * lctx |
    L_final1 of Stringa.char list * Syntax.x * lctx |
    L_final2 of Stringa.char list * Syntax.x * Syntax.s |
    L_match of Syntax.v * Stringa.char list * Syntax.x * lctx |
    L_compose of lctx * lctx
  type ms_def = MS_type_def of Syntax.type_def | MS_fun_def of Syntax.fun_def |
    MS_val_spec of
      Stringa.char list * Syntax.x * Syntax.b * Syntax.c * Syntax.tau
    | MS_register of Syntax.u * Syntax.tau * Syntax.v
  val cf : 'a -> Stringa.char list
  val mapi : (Arith.nat -> 'a -> 'b) -> 'a list -> 'b list
  val mk_atom_u : Arith.nat -> Nominal2_Base.atom
  val mk_u : Arith.nat -> Syntax.u
  val mk_atom_x : Arith.nat -> Nominal2_Base.atom
  val mk_x : Arith.nat -> Syntax.x
  val trace : Stringa.char list -> bool
  val eq_i_i : 'a HOL.equal -> 'a -> 'a -> unit Predicate.pred
  val eq_o_i : 'a -> 'a Predicate.pred
  val mk_stra : 'a -> string
  val mk_str : 'a -> Stringa.char list
  val option_map : ('a -> 'b option) -> 'a list -> 'b list
  val mk_xxx : SailAST.quant_item list -> (SailAST.kid * SailAST.kind) list
  val mk_match_aux :
    (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
      (Stringa.char list * Syntax.x) option) list ->
      Syntax.s list -> Syntax.branch_list
  val mk_match :
    Syntax.x ->
      (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
        (Stringa.char list * Syntax.x) option) list ->
        Syntax.s list -> Syntax.s
  val collect_ids_pexps :
    (unit Env.tannot_ext option) SailAST.pexp list -> SailAST.id list
  val mk_id_map :
    (unit Env.tannot_ext option) SailAST.pexp list ->
      (SailAST.id * Syntax.x) list
  val lctx_apply : lctx -> Syntax.s -> Syntax.s
  val mk_switch :
    Syntax.x ->
      (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
        (lctx * Syntax.x) option) list ->
        Syntax.s list -> Syntax.s
  val mk_type_vars :
    (SailAST.kid * SailAST.kind) list ->
      Syntax.ce -> (SailAST.kid * (SailAST.kind * Syntax.ce)) list
  val mk_tq_map :
    SailAST.typquant -> (SailAST.kid * (SailAST.kind * Syntax.ce)) list
  val lookup_kid :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.kid -> Syntax.ce option
  val mk_fresh_x : Arith.nat -> Arith.nat * Syntax.x
  val mk_pm_list :
    unit Env.env_ext ->
      SailAST.id ->
        (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
          (Stringa.char list * Syntax.x) option) list ->
          (SailAST.typ * Syntax.x) list ->
            (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
              (SailAST.typ * Syntax.x) list) list
  val extract_tan :
    unit Env.tannot_ext option ->
      (unit Env.tannot_ext option) SailAST.funcl list ->
        unit Env.tannot_ext option
  val get_len_i_o : SailAST.typ -> Syntax.v Predicate.pred
  val get_len_lit : SailAST.lit -> Syntax.v
  val b_of_typ_i_o : SailAST.typ -> Syntax.b Predicate.pred
  val extract_pexp :
    (unit Env.tannot_ext option) SailAST.funcl list ->
      (unit Env.tannot_ext option) SailAST.pexp_funcl list
  val lit_conv_i_o : SailAST.lit -> Syntax.l Predicate.pred
  val c_bool_conv_i_i_i_o_o_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.n_constraint ->
        Syntax.ce ->
          (Syntax.type_def list * (Syntax.gamma * Syntax.c)) Predicate.pred
  val ce_conv_i_i_o_o_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.nexp ->
        (Syntax.type_def list * (Syntax.gamma * Syntax.ce)) Predicate.pred
  val t_conv_raw_i_i_i_o_o_o_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.typ ->
        Syntax.ce ->
          (Syntax.type_def list * (Syntax.gamma * (Syntax.b * Syntax.c)))
            Predicate.pred
  val c_conv_i_i_o_o_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.n_constraint ->
        (Syntax.type_def list * (Syntax.gamma * Syntax.c)) Predicate.pred
  val t_conv_i_i_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.typ -> Syntax.tau Predicate.pred
  val add_to_pmctor :
    (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
      (Stringa.char list * Syntax.x) option) list ->
      (Stringa.char list * Syntax.x) option ->
        (unit Env.tannot_ext option) SailAST.pat list * Syntax.s ->
          (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
            (Stringa.char list * Syntax.x) option) list
  val mk_fresh_many : Arith.nat -> Arith.nat -> Arith.nat * Syntax.x list
  val mk_tq_c_aux_i_i_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.quant_item list -> Syntax.c Predicate.pred
  val mk_tq_c_i_i_o :
    (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
      SailAST.typquant -> Syntax.c Predicate.pred
  val def_funtyp_i_i_o_o_o :
    SailAST.typquant ->
      SailAST.typ -> (Syntax.b * (Syntax.c * Syntax.tau)) Predicate.pred
  val variant_conv_i_i_o :
    unit Env.env_ext ->
      SailAST.type_union list ->
        ((Stringa.char list * Syntax.tau) list) Predicate.pred
  val expand_ctor_i_i_i_i_i_o_o_o :
    Arith.nat ->
      unit Env.env_ext ->
        ((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list ->
          SailAST.id ->
            Syntax.x ->
              ((((unit Env.tannot_ext option) SailAST.pat list *
                  Syntax.s) list *
                 (Stringa.char list * Syntax.x) option) list *
                ((SailAST.id * Syntax.x) list * Arith.nat))
                Predicate.pred
  val fresh_vars_list : Arith.nat -> Arith.nat -> Arith.nat * Syntax.x list
  val expand_tuple_i_i_i_i_o_o_o :
    Arith.nat ->
      ((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list ->
        Arith.nat ->
          Syntax.x ->
            (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
              (Syntax.x list * Arith.nat))
              Predicate.pred
  val expand_vector_concat_i_i_i_i_o_o_o :
    Arith.nat ->
      Syntax.x ->
        Syntax.x ->
          (unit Env.tannot_ext option) SailAST.pat list ->
            (lctx * (Syntax.x * Arith.nat)) Predicate.pred
  val expand_lit_i_i_i_i_i_o_o_o :
    Arith.nat ->
      unit Env.env_ext ->
        (SailAST.id * Syntax.x) list ->
          ((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list ->
            Syntax.x ->
              ((((unit Env.tannot_ext option) SailAST.pat list *
                  Syntax.s) list *
                 (lctx * Syntax.x) option) list *
                ((SailAST.id * Syntax.x) list * Arith.nat))
                Predicate.pred
  val as_unpack_i_i_i_i_o_o :
    Arith.nat ->
      Syntax.x ->
        Syntax.x list -> Syntax.s -> (Syntax.s * Arith.nat) Predicate.pred
  val is_literal_base : SailAST.typ -> bool
  val conv_pattern_matrix_i_i_i_i_i_o_o :
    Arith.nat ->
      unit Env.env_ext ->
        (SailAST.id * Syntax.x) list ->
          ((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list ->
            (SailAST.typ * Syntax.x) list ->
              (Syntax.s * Arith.nat) Predicate.pred
  val conv_pattern_matrix_list_i_i_i_i_o_o :
    Arith.nat ->
      unit Env.env_ext ->
        (SailAST.id * Syntax.x) list ->
          (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
            (SailAST.typ * Syntax.x) list) list ->
            (Syntax.s list * Arith.nat) Predicate.pred
  val v_conv_i_i_i_o_o_o :
    unit Env.env_ext ->
      (SailAST.id * Syntax.x) list ->
        (unit Env.tannot_ext option) SailAST.exp ->
          (Syntax.type_def list * (Syntax.gamma * Syntax.v)) Predicate.pred
  val e_conv_i_i_i_i_o_o_o_o_o_o_o :
    Arith.nat ->
      (SailAST.id * Syntax.x) list ->
        (unit Env.tannot_ext option) SailAST.exp ->
          Syntax.x ->
            (Syntax.type_def list *
              (Syntax.fun_def list *
                (Syntax.bv FSet.fset *
                  (Syntax.gamma * (Syntax.delta * (lctx * Arith.nat))))))
              Predicate.pred
  val e_conv_list_i_i_i_i_o_o_o_o_o_o_o :
    Arith.nat ->
      (SailAST.id * Syntax.x) list ->
        (unit Env.tannot_ext option) SailAST.exp list ->
          Syntax.x ->
            (Syntax.type_def list *
              (Syntax.fun_def list *
                (Syntax.bv FSet.fset *
                  (Syntax.gamma * (Syntax.delta * (lctx * Arith.nat))))))
              Predicate.pred
  val pexp_list_conv_i_i_i_i_i_o_o :
    Arith.nat ->
      unit Env.env_ext ->
        (SailAST.id * Syntax.x) list ->
          (unit Env.tannot_ext option) SailAST.pexp list ->
            Syntax.x ->
              (((unit Env.tannot_ext option) SailAST.pat list * Syntax.s) list *
                Arith.nat)
                Predicate.pred
  val s_conv_i_i_i_o_o_o_o_o_o_o :
    Arith.nat ->
      (SailAST.id * Syntax.x) list ->
        (unit Env.tannot_ext option) SailAST.exp ->
          (Syntax.type_def list *
            (Syntax.fun_def list *
              (Syntax.bv FSet.fset *
                (Syntax.gamma * (Syntax.delta * (Syntax.s * Arith.nat))))))
            Predicate.pred
  val funcl_conv_i_i_i_o :
    unit Env.env_ext ->
      (SailAST.kid * (SailAST.kind * Syntax.ce)) list ->
        (unit Env.tannot_ext option) SailAST.pexp_funcl list ->
          Syntax.s Predicate.pred
  val lookup_fun_typ :
    unit Env.env_ext -> string -> (SailAST.typquant * SailAST.typ) option
  val def_conv_i_i_o :
    unit Env.env_ext ->
      (unit Env.tannot_ext option) SailAST.def -> (ms_def option) Predicate.pred
end = struct

type lctx = L_hole | L_continue | L_val of Syntax.v |
  L_let of Syntax.x * Syntax.e * lctx | L_if1 of Syntax.v * lctx * Syntax.s |
  L_if2 of Syntax.v * Syntax.s * lctx | L_if3 of Syntax.v * lctx * lctx |
  L_final1 of Stringa.char list * Syntax.x * lctx |
  L_final2 of Stringa.char list * Syntax.x * Syntax.s |
  L_match of Syntax.v * Stringa.char list * Syntax.x * lctx |
  L_compose of lctx * lctx;;

type ms_def = MS_type_def of Syntax.type_def | MS_fun_def of Syntax.fun_def |
  MS_val_spec of Stringa.char list * Syntax.x * Syntax.b * Syntax.c * Syntax.tau
  | MS_register of Syntax.u * Syntax.tau * Syntax.v;;

let rec cf x = (fun _ -> []) x;;

let rec mapi
  f xs =
    Lista.map (fun (a, b) -> f a b)
      (Lista.zip (Lista.upt Arith.Zero_nat (Lista.size_list xs)) xs);;

let rec mk_atom_u
  n = Nominal2_Base.Atom
        (Nominal2_Base.Sort
           ([Stringa.Chara (true, true, false, false, true, false, true, false);
              Stringa.Chara (true, false, false, true, true, true, true, false);
              Stringa.Chara (false, true, true, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false);
              Stringa.Chara
                (true, false, false, false, false, true, true, false);
              Stringa.Chara
                (false, false, false, true, true, true, true, false);
              Stringa.Chara
                (false, true, true, true, false, true, false, false);
              Stringa.Chara
                (true, false, true, false, true, true, true, false)],
             []),
          n);;

let rec mk_u xa = Syntax.Abs_u (mk_atom_u xa);;

let rec mk_atom_x
  n = Nominal2_Base.Atom
        (Nominal2_Base.Sort
           ([Stringa.Chara (true, true, false, false, true, false, true, false);
              Stringa.Chara (true, false, false, true, true, true, true, false);
              Stringa.Chara (false, true, true, true, false, true, true, false);
              Stringa.Chara
                (false, false, true, false, true, true, true, false);
              Stringa.Chara
                (true, false, false, false, false, true, true, false);
              Stringa.Chara
                (false, false, false, true, true, true, true, false);
              Stringa.Chara
                (false, true, true, true, false, true, false, false);
              Stringa.Chara
                (false, false, false, true, true, true, true, false)],
             []),
          n);;

let rec mk_x xa = Syntax.Abs_x (mk_atom_x xa);;

let rec trace s = (let _ = Utils2.trace (Stringa.implode s) in true);;

let rec eq_i_i _A
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (x, xaa) ->
        (if HOL.eq _A x xaa then Predicate.single () else Predicate.bot_pred));;

let rec eq_o_i xa = Predicate.bind (Predicate.single xa) Predicate.single;;

let rec mk_stra s = "";;

let rec mk_str t = Stringa.explode (mk_stra t);;

let rec option_map
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> option_map f xs
          | Some y -> y :: option_map f xs);;

let rec mk_xxx
  qi_list =
    option_map
      (fun a ->
        (match a
          with SailAST.QI_id (SailAST.KOpt_kind (kind, kid)) -> Some (kid, kind)
          | SailAST.QI_constraint _ -> None | SailAST.QI_constant _ -> None))
      qi_list;;

let rec mk_match_aux
  x0 x1 = match x0, x1 with
    [(uu, Some (dc, xa))], [sa] ->
      Syntax.AS_final (Syntax.AS_branch (dc, xa, sa))
    | (uv, Some (dc, xa)) :: v :: va, sa :: sas ->
        Syntax.AS_cons
          (Syntax.AS_branch (dc, xa, sa), mk_match_aux (v :: va) sas)
    | (uv, Some (dc, xa)) :: bs, sa :: v :: va ->
        Syntax.AS_cons
          (Syntax.AS_branch (dc, xa, sa), mk_match_aux bs (v :: va));;

let rec mk_match
  xa bs sa = match xa, bs, sa with xa, [(uu, None)], [sa] -> sa
    | xa, [], sa -> Syntax.AS_match (Syntax.V_var xa, mk_match_aux [] sa)
    | xa, (vb, Some vd) :: va, sa ->
        Syntax.AS_match (Syntax.V_var xa, mk_match_aux ((vb, Some vd) :: va) sa)
    | xa, v :: vb :: vc, sa ->
        Syntax.AS_match (Syntax.V_var xa, mk_match_aux (v :: vb :: vc) sa)
    | xa, bs, [] -> Syntax.AS_match (Syntax.V_var xa, mk_match_aux bs [])
    | xa, bs, v :: vb :: vc ->
        Syntax.AS_match (Syntax.V_var xa, mk_match_aux bs (v :: vb :: vc));;

let rec collect_ids_pexps
  pexps =
    Lista.maps
      (AstUtils.collect_pexp
        (fun a ->
          (match a with SailAST.P_lit (_, _) -> [] | SailAST.P_wild _ -> []
            | SailAST.P_or (_, _, _) -> [] | SailAST.P_not (_, _) -> []
            | SailAST.P_as (_, _, _) -> [] | SailAST.P_typ (_, _, _) -> []
            | SailAST.P_id (_, i) -> [i] | SailAST.P_var (_, _, _) -> []
            | SailAST.P_app (_, _, _) -> [] | SailAST.P_vector (_, _) -> []
            | SailAST.P_vector_concat (_, _) -> [] | SailAST.P_tup (_, _) -> []
            | SailAST.P_list (_, _) -> [] | SailAST.P_cons (_, _, _) -> []
            | SailAST.P_string_append (_, _) -> []))
        (fun a ->
          (match a with SailAST.E_block (_, _) -> []
            | SailAST.E_id (_, i) -> [i] | SailAST.E_lit (_, _) -> []
            | SailAST.E_cast (_, _, _) -> [] | SailAST.E_app (_, _, _) -> []
            | SailAST.E_app_infix (_, _, _, _) -> []
            | SailAST.E_tuple (_, _) -> [] | SailAST.E_if (_, _, _, _) -> []
            | SailAST.E_loop (_, _, _, _, _) -> []
            | SailAST.E_for (_, _, _, _, _, _, _) -> []
            | SailAST.E_vector (_, _) -> []
            | SailAST.E_vector_access (_, _, _) -> []
            | SailAST.E_vector_subrange (_, _, _, _) -> []
            | SailAST.E_vector_update (_, _, _, _) -> []
            | SailAST.E_vector_update_subrange (_, _, _, _, _) -> []
            | SailAST.E_vector_append (_, _, _) -> []
            | SailAST.E_list (_, _) -> [] | SailAST.E_cons (_, _, _) -> []
            | SailAST.E_record (_, _) -> []
            | SailAST.E_record_update (_, _, _) -> []
            | SailAST.E_field (_, _, _) -> [] | SailAST.E_case (_, _, _) -> []
            | SailAST.E_let (_, _, _) -> [] | SailAST.E_assign (_, _, _) -> []
            | SailAST.E_sizeof (_, _) -> [] | SailAST.E_return (_, _) -> []
            | SailAST.E_exit (_, _) -> [] | SailAST.E_ref (_, _) -> []
            | SailAST.E_throw (_, _) -> [] | SailAST.E_try (_, _, _) -> []
            | SailAST.E_assert (_, _, _) -> []
            | SailAST.E_var (_, _, _, _) -> []
            | SailAST.E_internal_plet (_, _, _, _) -> []
            | SailAST.E_internal_return (_, _) -> []
            | SailAST.E_internal_value (_, _) -> []
            | SailAST.E_constraint (_, _) -> [])))
      pexps;;

let rec mk_id_map
  ps = mapi (fun n i ->
              (i, mk_x (Arith.plus_nat
                         (Arith.times_nat
                           (Arith.nat_of_num (Arith.Bit0 Arith.One)) n)
                         Arith.one_nat)))
         (collect_ids_pexps ps);;

let rec lctx_apply
  x0 s = match x0, s with L_hole, s -> s
    | L_continue, s -> s
    | L_val va, uu -> Syntax.AS_val va
    | L_let (xa, ea, l), s -> Syntax.AS_let (xa, ea, lctx_apply l s)
    | L_if1 (va, l, sa), s -> Syntax.AS_if (va, lctx_apply l s, sa)
    | L_if2 (va, sa, l), s -> Syntax.AS_if (va, sa, lctx_apply l s)
    | L_if3 (va, l1, l2), s ->
        Syntax.AS_if (va, lctx_apply l1 s, lctx_apply l2 s)
    | L_match (va, dc, xa, l), s ->
        Syntax.AS_match
          (va, Syntax.AS_cons
                 (Syntax.AS_branch (dc, xa, lctx_apply l s),
                   Syntax.AS_final
                     (Syntax.AS_branch
                       (dc, xa, Syntax.AS_val (Syntax.V_lit Syntax.L_unit)))))
    | L_compose (l1, l2), s -> lctx_apply l1 (lctx_apply l2 s);;

let rec mk_switch
  xa x1 x2 = match xa, x1, x2 with
    xa, [(uu, Some (l, xb))], [sa] ->
      lctx_apply l
        (Syntax.AS_if
          (Syntax.V_var xb, sa, Syntax.AS_val (Syntax.V_lit Syntax.L_unit)))
    | xa, [(uv, None)], [sa] -> sa
    | xa, (uw, Some (l, xb)) :: v :: va, sa :: sas ->
        lctx_apply l
          (Syntax.AS_if (Syntax.V_var xb, sa, mk_switch xa (v :: va) sas))
    | xa, (uw, Some (l, xb)) :: ps, sa :: v :: va ->
        lctx_apply l
          (Syntax.AS_if (Syntax.V_var xb, sa, mk_switch xa ps (v :: va)));;

let rec mk_type_vars
  x0 uu = match x0, uu with [], uu -> []
    | [(kid, kind)], ce -> [(kid, (kind, ce))]
    | (kid, kind) :: k :: kv, ce ->
        (kid, (kind, Syntax.CE_fst ce)) ::
          mk_type_vars (k :: kv) (Syntax.CE_snd ce);;

let rec mk_tq_map
  = function SailAST.TypQ_no_forall -> []
    | SailAST.TypQ_tq qi_list ->
        mk_type_vars (mk_xxx qi_list)
          (Syntax.CE_fst (Syntax.CE_val (Syntax.V_var (mk_x Arith.one_nat))));;

let rec lookup_kid
  x0 uu = match x0, uu with [], uu -> None
    | (k1, (uv, ce)) :: tvs, k2 ->
        (if SailAST.equal_kid k1 k2 then Some ce else lookup_kid tvs k2);;

let rec mk_fresh_x
  ii = (Arith.plus_nat ii Arith.one_nat,
         mk_x (Arith.times_nat (Arith.plus_nat ii Arith.one_nat)
                (Arith.nat_of_num (Arith.Bit0 Arith.One))));;

let rec mk_pm_list
  env tyid pmctor bss =
    Lista.map
      (fun a ->
        (match a with (pm, None) -> (pm, bss)
          | (pm, Some (dc, xa)) ->
            (match
              Env.lookup_variant_env env tyid (SailAST.Id (Stringa.implode dc))
              with None ->
                (let Some _ =
                   Env.lookup_enum_env env (SailAST.Id (Stringa.implode dc)) in
                  (pm, (AstUtils.unit_typ, xa) :: bss))
              | Some typ -> (pm, (typ, xa) :: bss))))
      pmctor;;

let rec extract_tan
  tan x1 = match tan, x1 with tan, [] -> tan
    | tana, SailAST.FCL_Funcl (tan, uu, uv) :: fcls -> extract_tan tan fcls;;

let rec get_len_i_o
  x = Predicate.bind (Predicate.single x)
        (fun a ->
          (match a with SailAST.Typ_internal_unknown -> Predicate.bot_pred
            | SailAST.Typ_id _ -> Predicate.bot_pred
            | SailAST.Typ_var _ -> Predicate.bot_pred
            | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
            | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
            | SailAST.Typ_tup _ -> Predicate.bot_pred
            | SailAST.Typ_app (SailAST.Id _, []) -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_id _) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_var _) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, [SailAST.A_nexp (SailAST.Nexp_constant _)])
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id xa, [SailAST.A_nexp (SailAST.Nexp_constant i); _])
              -> (if ((xa : string) = "bitvector")
                   then Predicate.single
                          (Syntax.V_lit (Syntax.L_num (Arith.int_of_integer i)))
                   else Predicate.bot_pred)
            | SailAST.Typ_app
                (SailAST.Id _,
                  SailAST.A_nexp (SailAST.Nexp_constant _) :: _ :: _ :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_app (_, _)) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_times (_, _)) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_sum (_, _)) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_minus (_, _)) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_exp _) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app
                (SailAST.Id _, SailAST.A_nexp (SailAST.Nexp_neg _) :: _)
              -> Predicate.bot_pred
            | SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _) ->
              Predicate.bot_pred
            | SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _) ->
              Predicate.bot_pred
            | SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _) ->
              Predicate.bot_pred
            | SailAST.Typ_app (SailAST.Operator _, _) -> Predicate.bot_pred
            | SailAST.Typ_exist (_, _, _) -> Predicate.bot_pred));;

let rec get_len_lit
  = function
    SailAST.L_hex bs ->
      Syntax.V_lit
        (Syntax.L_num
          (Arith.times_inta
            (Arith.of_nat Arith.semiring_1_int
              (Lista.size_list (Stringa.explode bs)))
            (Arith.Pos (Arith.Bit0 (Arith.Bit0 Arith.One)))))
    | SailAST.L_bin bs ->
        Syntax.V_lit
          (Syntax.L_num
            (Arith.of_nat Arith.semiring_1_int
              (Lista.size_list (Stringa.explode bs))));;

let rec b_of_typ_i_o
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun xa ->
            (if SailAST.equal_typa xa AstUtils.unit_typ
              then Predicate.single Syntax.B_unit else Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                | SailAST.Typ_id _ -> Predicate.bot_pred
                | SailAST.Typ_var _ -> Predicate.bot_pred
                | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                | SailAST.Typ_tup _ -> Predicate.bot_pred
                | SailAST.Typ_app (SailAST.Id xa, _) ->
                  (if ((xa : string) = "atom_bool")
                    then Predicate.single Syntax.B_bool else Predicate.bot_pred)
                | SailAST.Typ_app (SailAST.Operator _, _) -> Predicate.bot_pred
                | SailAST.Typ_exist (_, _, _) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single x)
              (fun a ->
                (match a with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                  | SailAST.Typ_id _ -> Predicate.bot_pred
                  | SailAST.Typ_var _ -> Predicate.bot_pred
                  | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                  | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                  | SailAST.Typ_tup _ -> Predicate.bot_pred
                  | SailAST.Typ_app (SailAST.Id xa, _) ->
                    (if ((xa : string) = "atom")
                      then Predicate.single Syntax.B_int
                      else Predicate.bot_pred)
                  | SailAST.Typ_app (SailAST.Operator _, _) ->
                    Predicate.bot_pred
                  | SailAST.Typ_exist (_, _, _) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single x)
                (fun a ->
                  (match a
                    with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                    | SailAST.Typ_id _ -> Predicate.bot_pred
                    | SailAST.Typ_var _ -> Predicate.bot_pred
                    | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                    | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                    | SailAST.Typ_tup _ -> Predicate.bot_pred
                    | SailAST.Typ_app (SailAST.Id xa, _) ->
                      (if ((xa : string) = "bitvector")
                        then Predicate.single Syntax.B_bitvec
                        else Predicate.bot_pred)
                    | SailAST.Typ_app (SailAST.Operator _, _) ->
                      Predicate.bot_pred
                    | SailAST.Typ_exist (_, _, _) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single x)
                  (fun a ->
                    (match a
                      with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                      | SailAST.Typ_id _ -> Predicate.bot_pred
                      | SailAST.Typ_var _ -> Predicate.bot_pred
                      | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_tup [] -> Predicate.bot_pred
                      | SailAST.Typ_tup [_] -> Predicate.bot_pred
                      | SailAST.Typ_tup [t1; t2] ->
                        Predicate.bind (b_of_typ_i_o t1)
                          (fun xa ->
                            Predicate.bind (b_of_typ_i_o t2)
                              (fun xaa ->
                                Predicate.single (Syntax.B_pair (xa, xaa))))
                      | SailAST.Typ_tup (_ :: _ :: _ :: _) -> Predicate.bot_pred
                      | SailAST.Typ_app (_, _) -> Predicate.bot_pred
                      | SailAST.Typ_exist (_, _, _) -> Predicate.bot_pred)))
                (Predicate.bind (Predicate.single x)
                  (fun a ->
                    (match a
                      with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                      | SailAST.Typ_id (SailAST.Id tyid) ->
                        Predicate.single (Syntax.B_id (Stringa.explode tyid))
                      | SailAST.Typ_id (SailAST.Operator _) ->
                        Predicate.bot_pred
                      | SailAST.Typ_var _ -> Predicate.bot_pred
                      | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_tup _ -> Predicate.bot_pred
                      | SailAST.Typ_app (_, _) -> Predicate.bot_pred
                      | SailAST.Typ_exist (_, _, _) ->
                        Predicate.bot_pred)))))));;

let rec extract_pexp
  fcls = Lista.map (fun (SailAST.FCL_Funcl (_, _, pe)) -> pe) fcls;;

let rec lit_conv_i_o
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun a ->
            (match a with SailAST.L_unit -> Predicate.single Syntax.L_unit
              | SailAST.L_zero -> Predicate.bot_pred
              | SailAST.L_one -> Predicate.bot_pred
              | SailAST.L_true -> Predicate.bot_pred
              | SailAST.L_false -> Predicate.bot_pred
              | SailAST.L_num _ -> Predicate.bot_pred
              | SailAST.L_hex _ -> Predicate.bot_pred
              | SailAST.L_bin _ -> Predicate.bot_pred
              | SailAST.L_string _ -> Predicate.bot_pred
              | SailAST.L_undef -> Predicate.bot_pred
              | SailAST.L_real _ -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with SailAST.L_unit -> Predicate.bot_pred
                | SailAST.L_zero -> Predicate.bot_pred
                | SailAST.L_one -> Predicate.bot_pred
                | SailAST.L_true -> Predicate.single Syntax.L_true
                | SailAST.L_false -> Predicate.bot_pred
                | SailAST.L_num _ -> Predicate.bot_pred
                | SailAST.L_hex _ -> Predicate.bot_pred
                | SailAST.L_bin _ -> Predicate.bot_pred
                | SailAST.L_string _ -> Predicate.bot_pred
                | SailAST.L_undef -> Predicate.bot_pred
                | SailAST.L_real _ -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single x)
              (fun a ->
                (match a with SailAST.L_unit -> Predicate.bot_pred
                  | SailAST.L_zero -> Predicate.bot_pred
                  | SailAST.L_one -> Predicate.bot_pred
                  | SailAST.L_true -> Predicate.bot_pred
                  | SailAST.L_false -> Predicate.single Syntax.L_false
                  | SailAST.L_num _ -> Predicate.bot_pred
                  | SailAST.L_hex _ -> Predicate.bot_pred
                  | SailAST.L_bin _ -> Predicate.bot_pred
                  | SailAST.L_string _ -> Predicate.bot_pred
                  | SailAST.L_undef -> Predicate.bot_pred
                  | SailAST.L_real _ -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single x)
                (fun a ->
                  (match a with SailAST.L_unit -> Predicate.bot_pred
                    | SailAST.L_zero -> Predicate.bot_pred
                    | SailAST.L_one -> Predicate.bot_pred
                    | SailAST.L_true -> Predicate.bot_pred
                    | SailAST.L_false -> Predicate.bot_pred
                    | SailAST.L_num _ -> Predicate.bot_pred
                    | SailAST.L_hex _ -> Predicate.bot_pred
                    | SailAST.L_bin bs ->
                      Predicate.single
                        (Syntax.L_bitvec
                          (Lista.map
                            (fun b ->
                              (if Stringa.equal_chara b
                                    (Stringa.Chara
                                      (true, false, false, false, true, true,
false, false))
                                then Syntax.BitOne else Syntax.BitZero))
                            (Stringa.explode bs)))
                    | SailAST.L_string _ -> Predicate.bot_pred
                    | SailAST.L_undef -> Predicate.bot_pred
                    | SailAST.L_real _ -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single x)
                  (fun a ->
                    (match a with SailAST.L_unit -> Predicate.bot_pred
                      | SailAST.L_zero -> Predicate.bot_pred
                      | SailAST.L_one -> Predicate.bot_pred
                      | SailAST.L_true -> Predicate.bot_pred
                      | SailAST.L_false -> Predicate.bot_pred
                      | SailAST.L_num _ -> Predicate.bot_pred
                      | SailAST.L_hex _ -> Predicate.single (Syntax.L_bitvec [])
                      | SailAST.L_bin _ -> Predicate.bot_pred
                      | SailAST.L_string _ -> Predicate.bot_pred
                      | SailAST.L_undef -> Predicate.bot_pred
                      | SailAST.L_real _ -> Predicate.bot_pred)))
                (Predicate.bind (Predicate.single x)
                  (fun a ->
                    (match a with SailAST.L_unit -> Predicate.bot_pred
                      | SailAST.L_zero -> Predicate.bot_pred
                      | SailAST.L_one -> Predicate.bot_pred
                      | SailAST.L_true -> Predicate.bot_pred
                      | SailAST.L_false -> Predicate.bot_pred
                      | SailAST.L_num ii ->
                        Predicate.single
                          (Syntax.L_num (Arith.int_of_integer ii))
                      | SailAST.L_hex _ -> Predicate.bot_pred
                      | SailAST.L_bin _ -> Predicate.bot_pred
                      | SailAST.L_string _ -> Predicate.bot_pred
                      | SailAST.L_undef -> Predicate.bot_pred
                      | SailAST.L_real _ -> Predicate.bot_pred)))))));;

let rec c_bool_conv_i_i_i_o_o_o
  x xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xa, xb)))
        (fun a ->
          (match a with (_, (SailAST.NC_equal (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_bounded_ge (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_bounded_gt (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_bounded_le (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_bounded_lt (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_not_equal (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
            | (_, (SailAST.NC_true, ce)) ->
              Predicate.single
                ([], (Syntax.GNil,
                       Syntax.C_eq
                         (ce, Syntax.CE_val (Syntax.V_lit Syntax.L_true))))
            | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xa, xb)))
          (fun a ->
            (match a
              with (_, (SailAST.NC_equal (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_bounded_ge (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_bounded_gt (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_bounded_le (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_bounded_lt (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_not_equal (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
              | (_, (SailAST.NC_false, ce)) ->
                Predicate.single
                  ([], (Syntax.GNil,
                         Syntax.C_eq
                           (ce, Syntax.CE_val
                                  (Syntax.V_lit Syntax.L_false)))))))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xa, xb)))
            (fun a ->
              (match a
                with (_, (SailAST.NC_equal (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_bounded_ge (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_bounded_gt (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_bounded_le (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_bounded_lt (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_not_equal (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
                | (env, (SailAST.NC_var k, ce)) ->
                  Predicate.bind (eq_o_i (lookup_kid env k))
                    (fun aa ->
                      (match aa with None -> Predicate.bot_pred
                        | Some cea ->
                          Predicate.single
                            ([], (Syntax.GNil, Syntax.C_eq (ce, cea)))))
                | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xa, xb)))
              (fun a ->
                (match a
                  with (_, (SailAST.NC_equal (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_bounded_ge (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_bounded_gt (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_bounded_le (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_bounded_lt (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_not_equal (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_app (SailAST.Id _, []), _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.NC_app (SailAST.Id _, SailAST.A_nexp _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app (SailAST.Id _, SailAST.A_typ _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app (SailAST.Id _, SailAST.A_order _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_equal (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_bounded_ge (_, _)) ::
                               _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_bounded_gt (_, _)) ::
                               _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_bounded_le (_, _)) ::
                               _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_bounded_lt (_, _)) ::
                               _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_not_equal (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_set (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_or (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_and (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_app (_, _)) :: _),
                          _))
                    -> Predicate.bot_pred
                  | (env, (SailAST.NC_app
                             (SailAST.Id xc,
                               [SailAST.A_bool (SailAST.NC_var k)]),
                            ce))
                    -> Predicate.bind (eq_o_i (lookup_kid env k))
                         (fun aa ->
                           (match aa with None -> Predicate.bot_pred
                             | Some cea ->
                               (if ((xc : string) = "not")
                                 then Predicate.single
([], (Syntax.GNil, Syntax.C_not (Syntax.C_eq (ce, cea))))
                                 else Predicate.bot_pred)))
                  | (_, (SailAST.NC_app
                           (SailAST.Id _,
                             SailAST.A_bool (SailAST.NC_var _) :: _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _, SailAST.A_bool SailAST.NC_true :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app
                           (SailAST.Id _, SailAST.A_bool SailAST.NC_false :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.NC_app (SailAST.Operator _, _), _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                  | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, (xa, xb)))
                (fun a ->
                  (match a
                    with (_, (SailAST.NC_equal (_, _), _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_bounded_ge (_, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_bounded_gt (_, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_bounded_le (_, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_bounded_lt (_, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_not_equal (_, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_equal (_, _), _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_bounded_ge (_, _), _), _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_bounded_gt (_, _), _), _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_bounded_le (_, _), _), _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_bounded_lt (_, _), _), _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_not_equal (_, _), _), _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_set (_, _), _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_or (_, _), _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_and (_, _), _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_app (_, _), _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_equal (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_bounded_ge (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_bounded_gt (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_bounded_le (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_bounded_lt (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_not_equal (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_set (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_or (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_and (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and
                             (SailAST.NC_var _, SailAST.NC_app (_, _)),
                            _))
                      -> Predicate.bot_pred
                    | (env, (SailAST.NC_and
                               (SailAST.NC_var k1, SailAST.NC_var k2),
                              ce))
                      -> Predicate.bind (eq_o_i (lookup_kid env k1))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some ce1 ->
                                 Predicate.bind (eq_o_i (lookup_kid env k2))
                                   (fun ab ->
                                     (match ab with None -> Predicate.bot_pred
                                       | Some ce2 ->
 Predicate.single
   ([], (Syntax.GNil,
          Syntax.C_conj (Syntax.C_eq (ce, ce1), Syntax.C_eq (ce, ce2))))))))
                    | (_, (SailAST.NC_and (SailAST.NC_var _, SailAST.NC_true),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_var _, SailAST.NC_false),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_true, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_and (SailAST.NC_false, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                    | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, (xa, xb)))
                  (fun a ->
                    (match a
                      with (_, (SailAST.NC_equal (SailAST.Nexp_id _, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_id _),
                              _))
                        -> Predicate.bot_pred
                      | (env, (SailAST.NC_equal
                                 (SailAST.Nexp_var k1, SailAST.Nexp_var k2),
                                ce))
                        -> Predicate.bind (eq_o_i (lookup_kid env k1))
                             (fun aa ->
                               (match aa with None -> Predicate.bot_pred
                                 | Some ce1 ->
                                   Predicate.bind (eq_o_i (lookup_kid env k2))
                                     (fun ab ->
                                       (match ab with None -> Predicate.bot_pred
 | Some ce2 ->
   Predicate.single
     ([], (Syntax.GNil,
            Syntax.C_disj
              (Syntax.C_conj
                 (Syntax.C_eq (ce, Syntax.CE_val (Syntax.V_lit Syntax.L_true)),
                   Syntax.C_eq (ce1, ce2)),
                Syntax.C_conj
                  (Syntax.C_eq
                     (ce, Syntax.CE_val (Syntax.V_lit Syntax.L_false)),
                    Syntax.C_not (Syntax.C_eq (ce1, ce2))))))))))
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_constant _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_app (_, _)),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_times (_, _)),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_sum (_, _)),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_minus (_, _)),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_exp _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal
                               (SailAST.Nexp_var _, SailAST.Nexp_neg _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_constant _, _), _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_app (_, _), _), _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_times (_, _), _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_sum (_, _), _), _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_minus (_, _), _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_exp _, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_equal (SailAST.Nexp_neg _, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_bounded_ge (_, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_bounded_gt (_, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_bounded_le (_, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_bounded_lt (_, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_not_equal (_, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                      | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, (xa, xb)))
                    (fun a ->
                      (match a
                        with (_, (SailAST.NC_equal (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_ge (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt (SailAST.Nexp_id _, _), _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_id _),
                                _))
                          -> Predicate.bot_pred
                        | (env, (SailAST.NC_bounded_gt
                                   (SailAST.Nexp_var k1, SailAST.Nexp_var k2),
                                  ce))
                          -> Predicate.bind (eq_o_i (lookup_kid env k1))
                               (fun aa ->
                                 (match aa with None -> Predicate.bot_pred
                                   | Some ce1 ->
                                     Predicate.bind (eq_o_i (lookup_kid env k2))
                                       (fun ab ->
 (match ab with None -> Predicate.bot_pred
   | Some ce2 ->
     Predicate.single
       ([], (Syntax.GNil,
              Syntax.C_not
                (Syntax.C_eq (ce, Syntax.CE_op (Syntax.LEq, ce1, ce2)))))))))
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_constant _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_app (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _,
                                   SailAST.Nexp_times (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_sum (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _,
                                   SailAST.Nexp_minus (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_exp _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_var _, SailAST.Nexp_neg _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_constant _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_app (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_times (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_sum (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt
                                 (SailAST.Nexp_minus (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt (SailAST.Nexp_exp _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt (SailAST.Nexp_neg _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_le (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_not_equal (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_false, _)) -> Predicate.bot_pred)))
                  (Predicate.bind (Predicate.single (x, (xa, xb)))
                    (fun a ->
                      (match a
                        with (_, (SailAST.NC_equal (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_ge (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_gt (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_le (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt (SailAST.Nexp_id _, _), _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_id _),
                                _))
                          -> Predicate.bot_pred
                        | (env, (SailAST.NC_bounded_lt
                                   (SailAST.Nexp_var k1, SailAST.Nexp_var k2),
                                  ce))
                          -> Predicate.bind (eq_o_i (lookup_kid env k1))
                               (fun aa ->
                                 (match aa with None -> Predicate.bot_pred
                                   | Some ce1 ->
                                     Predicate.bind (eq_o_i (lookup_kid env k2))
                                       (fun ab ->
 (match ab with None -> Predicate.bot_pred
   | Some ce2 ->
     Predicate.single
       ([], (Syntax.GNil,
              Syntax.C_eq (ce, Syntax.CE_op (Syntax.LEq, ce2, ce1))))))))
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_constant _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_app (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _,
                                   SailAST.Nexp_times (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_sum (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _,
                                   SailAST.Nexp_minus (_, _)),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_exp _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_var _, SailAST.Nexp_neg _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_constant _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_app (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_times (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_sum (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt
                                 (SailAST.Nexp_minus (_, _), _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt (SailAST.Nexp_exp _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_bounded_lt (SailAST.Nexp_neg _, _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.NC_not_equal (_, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.NC_set (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_or (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_and (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_app (_, _), _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_var _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_true, _)) -> Predicate.bot_pred
                        | (_, (SailAST.NC_false, _)) ->
                          Predicate.bot_pred)))))))));;

let rec ce_conv_i_i_o_o_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, SailAST.Nexp_id _) -> Predicate.bot_pred
            | (_, SailAST.Nexp_var _) -> Predicate.bot_pred
            | (_, SailAST.Nexp_constant _) -> Predicate.bot_pred
            | (_, SailAST.Nexp_app (_, _)) -> Predicate.bot_pred
            | (_, SailAST.Nexp_times (_, _)) -> Predicate.bot_pred
            | (env, SailAST.Nexp_sum (ne1, ne2)) ->
              Predicate.bind (ce_conv_i_i_o_o_o env ne1)
                (fun (t1, (g1, ca1)) ->
                  Predicate.bind (ce_conv_i_i_o_o_o env ne2)
                    (fun (t2, (g2, ca2)) ->
                      Predicate.single
                        (t1 @ t2,
                          (Syntax.append_g g1 g2,
                            Syntax.CE_op (Syntax.Plus, ca1, ca2)))))
            | (_, SailAST.Nexp_minus (_, _)) -> Predicate.bot_pred
            | (_, SailAST.Nexp_exp _) -> Predicate.bot_pred
            | (_, SailAST.Nexp_neg _) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, SailAST.Nexp_id _) -> Predicate.bot_pred
              | (_, SailAST.Nexp_var _) -> Predicate.bot_pred
              | (_, SailAST.Nexp_constant ii) ->
                Predicate.single
                  ([], (Syntax.GNil,
                         Syntax.CE_val
                           (Syntax.V_lit
                             (Syntax.L_num (Arith.int_of_integer ii)))))
              | (_, SailAST.Nexp_app (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_times (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_sum (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_minus (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_exp _) -> Predicate.bot_pred
              | (_, SailAST.Nexp_neg _) -> Predicate.bot_pred)))
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, SailAST.Nexp_id _) -> Predicate.bot_pred
              | (env, SailAST.Nexp_var k) ->
                Predicate.bind (eq_o_i (lookup_kid env k))
                  (fun aa ->
                    (match aa with None -> Predicate.bot_pred
                      | Some ce -> Predicate.single ([], (Syntax.GNil, ce))))
              | (_, SailAST.Nexp_constant _) -> Predicate.bot_pred
              | (_, SailAST.Nexp_app (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_times (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_sum (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_minus (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Nexp_exp _) -> Predicate.bot_pred
              | (_, SailAST.Nexp_neg _) -> Predicate.bot_pred))));;

let rec t_conv_raw_i_i_i_o_o_o_o
  x xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xa, xb)))
        (fun (_, (xc, ce)) ->
          (if SailAST.equal_typa xc AstUtils.unit_typ
            then Predicate.single
                   ([], (Syntax.GNil,
                          (Syntax.B_unit,
                            Syntax.C_eq
                              (ce, Syntax.CE_val
                                     (Syntax.V_lit Syntax.L_unit)))))
            else Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xa, xb)))
          (fun (_, (xc, _)) ->
            (if SailAST.equal_typa xc AstUtils.int_typ
              then Predicate.single
                     ([], (Syntax.GNil, (Syntax.B_int, Syntax.C_true)))
              else Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xa, xb)))
            (fun (_, (xc, _)) ->
              (if SailAST.equal_typa xc AstUtils.bool_all_typ
                then Predicate.single
                       ([], (Syntax.GNil, (Syntax.B_bool, Syntax.C_true)))
                else Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xa, xb)))
              (fun a ->
                (match a
                  with (_, (SailAST.Typ_internal_unknown, _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.Typ_fn (_, _, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.Typ_bidir (_, _, _), _)) -> Predicate.bot_pred
                  | (_, (SailAST.Typ_tup _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.Typ_app (SailAST.Id _, []), _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.Typ_app (SailAST.Id _, SailAST.A_nexp _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (env, (SailAST.Typ_app (SailAST.Id xc, [SailAST.A_bool nc]),
                            ce))
                    -> Predicate.bind (c_bool_conv_i_i_i_o_o_o env nc ce)
                         (fun (t, (g, ca)) ->
                           (if ((xc : string) = "atom_bool")
                             then Predicate.single (t, (g, (Syntax.B_bool, ca)))
                             else Predicate.bot_pred))
                  | (_, (SailAST.Typ_app
                           (SailAST.Id _, SailAST.A_bool _ :: _ :: _),
                          _))
                    -> Predicate.bot_pred
                  | (_, (SailAST.Typ_app (SailAST.Operator _, _), _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                    Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, (xa, xb)))
                (fun a ->
                  (match a
                    with (_, (SailAST.Typ_internal_unknown, _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.Typ_fn (_, _, _), _)) -> Predicate.bot_pred
                    | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.Typ_tup _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.Typ_app (SailAST.Id _, []), _)) ->
                      Predicate.bot_pred
                    | (env, (SailAST.Typ_app
                               (SailAST.Id xc, [SailAST.A_nexp nexp]),
                              ce))
                      -> Predicate.bind (ce_conv_i_i_o_o_o env nexp)
                           (fun (t, (g, ce2)) ->
                             (if ((xc : string) = "atom")
                               then Predicate.single
                                      (t,
(g, (Syntax.B_int, Syntax.C_eq (ce, ce2))))
                               else Predicate.bot_pred))
                    | (_, (SailAST.Typ_app
                             (SailAST.Id _, SailAST.A_nexp _ :: _ :: _),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.Typ_app
                             (SailAST.Id _, SailAST.A_order _ :: _),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.Typ_app
                             (SailAST.Id _, SailAST.A_bool _ :: _),
                            _))
                      -> Predicate.bot_pred
                    | (_, (SailAST.Typ_app (SailAST.Operator _, _), _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                      Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, (xa, xb)))
                  (fun a ->
                    (match a
                      with (_, (SailAST.Typ_internal_unknown, _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.Typ_fn (_, _, _), _)) -> Predicate.bot_pred
                      | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.Typ_tup _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.Typ_app (SailAST.Id _, []), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.Typ_app (SailAST.Id _, [SailAST.A_nexp _]),
                              _))
                        -> Predicate.bot_pred
                      | (env, (SailAST.Typ_app
                                 (SailAST.Id xc, [SailAST.A_nexp nexp; _]),
                                ce))
                        -> Predicate.bind (ce_conv_i_i_o_o_o env nexp)
                             (fun (t, (g, ce2)) ->
                               (if ((xc : string) = "bitvector")
                                 then Predicate.single
(t, (g, (Syntax.B_bitvec, Syntax.C_eq (Syntax.CE_len ce, ce2))))
                                 else Predicate.bot_pred))
                      | (_, (SailAST.Typ_app
                               (SailAST.Id _, SailAST.A_nexp _ :: _ :: _ :: _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.Typ_app
                               (SailAST.Id _, SailAST.A_typ _ :: _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.Typ_app
                               (SailAST.Id _, SailAST.A_order _ :: _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.Typ_app
                               (SailAST.Id _, SailAST.A_bool _ :: _),
                              _))
                        -> Predicate.bot_pred
                      | (_, (SailAST.Typ_app (SailAST.Operator _, _), _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                        Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, (xa, xb)))
                    (fun a ->
                      (match a
                        with (_, (SailAST.Typ_internal_unknown, _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.Typ_fn (_, _, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.Typ_tup _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app (SailAST.Id _, []), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                _))
                          -> Predicate.bot_pred
                        | (env, (SailAST.Typ_app
                                   (SailAST.Id xc,
                                     [SailAST.A_nexp nexp1;
                                       SailAST.A_nexp nexp2]),
                                  ce))
                          -> Predicate.bind (ce_conv_i_i_o_o_o env nexp1)
                               (fun (t1, (g1, ce1)) ->
                                 Predicate.bind (ce_conv_i_i_o_o_o env nexp2)
                                   (fun (t2, (g2, ce2)) ->
                                     (if ((xc : string) = "range")
                                       then Predicate.single
      (t1 @ t2,
        (Syntax.append_g g1 g2,
          (Syntax.B_bool,
            Syntax.C_conj
              (Syntax.C_eq
                 (Syntax.CE_op (Syntax.LEq, ce1, ce),
                   Syntax.CE_val (Syntax.V_lit Syntax.L_true)),
                Syntax.C_eq
                  (Syntax.CE_val (Syntax.V_lit Syntax.L_true),
                    Syntax.CE_op (Syntax.LEq, ce, ce2))))))
                                       else Predicate.bot_pred)))
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _,
                                   SailAST.A_nexp _ ::
                                     SailAST.A_nexp _ :: _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _,
                                   SailAST.A_nexp _ :: SailAST.A_typ _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _,
                                   SailAST.A_nexp _ :: SailAST.A_order _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _,
                                   SailAST.A_nexp _ :: SailAST.A_bool _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_typ _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_order _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_bool _ :: _),
                                _))
                          -> Predicate.bot_pred
                        | (_, (SailAST.Typ_app (SailAST.Operator _, _), _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                          Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, (xa, xb)))
                      (fun a ->
                        (match a
                          with (_, (SailAST.Typ_internal_unknown, _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.Typ_fn (_, _, _), _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.Typ_tup [], _)) -> Predicate.bot_pred
                          | (env, (SailAST.Typ_tup [t1], ce)) ->
                            Predicate.bind (t_conv_raw_i_i_i_o_o_o_o env t1 ce)
                              (fun (t, (g, (ba1, ca1))) ->
                                Predicate.single (t, (g, (ba1, ca1))))
                          | (_, (SailAST.Typ_tup (_ :: _ :: _), _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.Typ_app (_, _), _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                            Predicate.bot_pred)))
                    (Predicate.sup_pred
                      (Predicate.bind (Predicate.single (x, (xa, xb)))
                        (fun a ->
                          (match a
                            with (_, (SailAST.Typ_internal_unknown, _)) ->
                              Predicate.bot_pred
                            | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                            | (_, (SailAST.Typ_var _, _)) -> Predicate.bot_pred
                            | (_, (SailAST.Typ_fn (_, _, _), _)) ->
                              Predicate.bot_pred
                            | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                              Predicate.bot_pred
                            | (_, (SailAST.Typ_tup [], _)) -> Predicate.bot_pred
                            | (_, (SailAST.Typ_tup [_], _)) ->
                              Predicate.bot_pred
                            | (env, (SailAST.Typ_tup (t1 :: t2 :: ts), ce)) ->
                              Predicate.bind
                                (t_conv_raw_i_i_i_o_o_o_o env t1
                                  (Syntax.CE_fst ce))
                                (fun (t1a, (g1, (ba1, _))) ->
                                  Predicate.bind
                                    (t_conv_raw_i_i_i_o_o_o_o env
                                      (SailAST.Typ_tup (t2 :: ts))
                                      (Syntax.CE_snd ce))
                                    (fun (t2a, (g2, (ba2, _))) ->
                                      Predicate.single
(t1a @ t2a,
  (Syntax.append_g g1 g2, (Syntax.B_pair (ba1, ba2), Syntax.C_true)))))
                            | (_, (SailAST.Typ_app (_, _), _)) ->
                              Predicate.bot_pred
                            | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                              Predicate.bot_pred)))
                      (Predicate.sup_pred
                        (Predicate.bind (Predicate.single (x, (xa, xb)))
                          (fun a ->
                            (match a
                              with (_, (SailAST.Typ_internal_unknown, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_id (SailAST.Id tyid), _)) ->
                                Predicate.single
                                  ([], (Syntax.GNil,
 (Syntax.B_id (Stringa.explode tyid), Syntax.C_true)))
                              | (_, (SailAST.Typ_id (SailAST.Operator _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_var _, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_fn (_, _, _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_tup _, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_app (_, _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                                Predicate.bot_pred)))
                        (Predicate.bind (Predicate.single (x, (xa, xb)))
                          (fun a ->
                            (match a
                              with (_, (SailAST.Typ_internal_unknown, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_id _, _)) -> Predicate.bot_pred
                              | (_, (SailAST.Typ_var _, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_fn (_, _, _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_bidir (_, _, _), _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_tup _, _)) ->
                                Predicate.bot_pred
                              | (_, (SailAST.Typ_app (_, []), _)) ->
                                Predicate.bot_pred
                              | (env, (SailAST.Typ_app
 (tfn, [SailAST.A_nexp ne]),
ce))
                                -> Predicate.bind
                                     (Predicate.if_pred
                                       (trace
 ([Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (true, true, false, false, false, true, true, false);
    Stringa.Chara (true, true, true, true, false, true, true, false);
    Stringa.Chara (false, true, true, true, false, true, true, false);
    Stringa.Chara (false, true, true, false, true, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (false, true, false, false, true, true, true, false);
    Stringa.Chara (true, false, false, false, false, true, true, false);
    Stringa.Chara (true, true, true, false, true, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, false, true, false, true, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (false, false, true, true, false, true, true, false);
    Stringa.Chara (true, false, true, false, false, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (true, false, false, true, false, true, true, false);
    Stringa.Chara (true, false, true, true, false, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (false, false, true, true, false, true, true, false);
    Stringa.Chara (true, false, false, true, false, true, true, false);
    Stringa.Chara (true, true, false, false, false, true, true, false);
    Stringa.Chara (true, false, false, true, false, true, true, false);
    Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (false, true, true, true, false, true, true, false);
    Stringa.Chara (true, false, true, false, false, true, true, false);
    Stringa.Chara (false, false, false, true, true, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (true, false, false, true, false, false, true, false)] @
   ShowAST.shows_prec_id Arith.Zero_nat tfn [])))
                                     (fun () ->
                                       Predicate.bind
 (eq_i_i SailAST.equal_id tfn (SailAST.Id "implicit"))
 (fun () ->
   Predicate.bind
     (t_conv_raw_i_i_i_o_o_o_o env
       (SailAST.Typ_app (SailAST.Id "atom", [SailAST.A_nexp ne])) ce)
     (fun (t, (g, (ba1, ca1))) -> Predicate.single (t, (g, (ba1, ca1))))))
                              | (_, (SailAST.Typ_app
                                       (_, SailAST.A_nexp _ :: _ :: _),
                                      _))
                                -> Predicate.bot_pred
                              | (_, (SailAST.Typ_app (_, SailAST.A_typ _ :: _),
                                      _))
                                -> Predicate.bot_pred
                              | (_, (SailAST.Typ_app
                                       (_, SailAST.A_order _ :: _),
                                      _))
                                -> Predicate.bot_pred
                              | (_, (SailAST.Typ_app (_, SailAST.A_bool _ :: _),
                                      _))
                                -> Predicate.bot_pred
                              | (_, (SailAST.Typ_exist (_, _, _), _)) ->
                                Predicate.bot_pred))))))))))));;

let rec c_conv_i_i_o_o_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a
            with (g, SailAST.NC_equal (cep1, cep2)) ->
              Predicate.bind (ce_conv_i_i_o_o_o g cep1)
                (fun (t1, (g1, cea1)) ->
                  Predicate.bind (ce_conv_i_i_o_o_o g cep2)
                    (fun (t2, (g2, cea2)) ->
                      Predicate.single
                        (t1 @ t2,
                          (Syntax.append_g g1 g2, Syntax.C_eq (cea1, cea2)))))
            | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
            | (_, SailAST.NC_var _) -> Predicate.bot_pred
            | (_, SailAST.NC_true) -> Predicate.bot_pred
            | (_, SailAST.NC_false) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
              | (g, SailAST.NC_bounded_ge (cep1, cep2)) ->
                Predicate.bind (ce_conv_i_i_o_o_o g cep1)
                  (fun (t1, (g1, cea1)) ->
                    Predicate.bind (ce_conv_i_i_o_o_o g cep2)
                      (fun (t2, (g2, cea2)) ->
                        Predicate.single
                          (t1 @ t2,
                            (Syntax.append_g g1 g2,
                              Syntax.C_eq
                                (Syntax.CE_op (Syntax.LEq, cea2, cea1),
                                  Syntax.CE_val
                                    (Syntax.V_lit Syntax.L_true))))))
              | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
              | (_, SailAST.NC_var _) -> Predicate.bot_pred
              | (_, SailAST.NC_true) -> Predicate.bot_pred
              | (_, SailAST.NC_false) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
                | (g, SailAST.NC_bounded_le (cep1, cep2)) ->
                  Predicate.bind (ce_conv_i_i_o_o_o g cep1)
                    (fun (t1, (g1, cea1)) ->
                      Predicate.bind (ce_conv_i_i_o_o_o g cep2)
                        (fun (t2, (g2, cea2)) ->
                          Predicate.single
                            (t1 @ t2,
                              (Syntax.append_g g1 g2,
                                Syntax.C_eq
                                  (Syntax.CE_op (Syntax.LEq, cea1, cea2),
                                    Syntax.CE_val
                                      (Syntax.V_lit Syntax.L_true))))))
                | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
                | (_, SailAST.NC_var _) -> Predicate.bot_pred
                | (_, SailAST.NC_true) -> Predicate.bot_pred
                | (_, SailAST.NC_false) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.NC_var _) -> Predicate.bot_pred
                  | (_, SailAST.NC_true) ->
                    Predicate.single ([], (Syntax.GNil, Syntax.C_true))
                  | (_, SailAST.NC_false) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a
                    with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.NC_var _) -> Predicate.bot_pred
                    | (_, SailAST.NC_true) -> Predicate.bot_pred
                    | (_, SailAST.NC_false) ->
                      Predicate.single ([], (Syntax.GNil, Syntax.C_false)))))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a
                      with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_or (_, _)) -> Predicate.bot_pred
                      | (g, SailAST.NC_and (cp1, cp2)) ->
                        Predicate.bind (c_conv_i_i_o_o_o g cp1)
                          (fun (t1, (g1, ca1)) ->
                            Predicate.bind (c_conv_i_i_o_o_o g cp2)
                              (fun (t2, (g2, ca2)) ->
                                Predicate.single
                                  (t1 @ t2,
                                    (Syntax.append_g g1 g2,
                                      Syntax.C_conj (ca1, ca2)))))
                      | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_var _) -> Predicate.bot_pred
                      | (_, SailAST.NC_true) -> Predicate.bot_pred
                      | (_, SailAST.NC_false) -> Predicate.bot_pred)))
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a
                      with (_, SailAST.NC_equal (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_ge (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_gt (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_le (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_bounded_lt (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_not_equal (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_set (_, _)) -> Predicate.bot_pred
                      | (g, SailAST.NC_or (cp1, cp2)) ->
                        Predicate.bind (c_conv_i_i_o_o_o g cp1)
                          (fun (t1, (g1, ca1)) ->
                            Predicate.bind (c_conv_i_i_o_o_o g cp2)
                              (fun (t2, (g2, ca2)) ->
                                Predicate.single
                                  (t1 @ t2,
                                    (Syntax.append_g g1 g2,
                                      Syntax.C_disj (ca1, ca2)))))
                      | (_, SailAST.NC_and (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_app (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.NC_var _) -> Predicate.bot_pred
                      | (_, SailAST.NC_true) -> Predicate.bot_pred
                      | (_, SailAST.NC_false) -> Predicate.bot_pred))))))));;

let rec t_conv_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun (env, t) ->
          Predicate.bind
            (t_conv_raw_i_i_i_o_o_o_o env t
              (Syntax.CE_val (Syntax.V_var (mk_x Arith.Zero_nat))))
            (fun (_, (_, (ba, ca))) ->
              Predicate.single
                (Syntax.T_refined_type (mk_x Arith.Zero_nat, ba, ca)))))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
            | (_, SailAST.Typ_id _) -> Predicate.bot_pred
            | (_, SailAST.Typ_var _) -> Predicate.bot_pred
            | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
            | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_exist ([], _, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_exist
                    (SailAST.KOpt_kind (SailAST.K_type, _) :: _, _, _))
              -> Predicate.bot_pred
            | (env, SailAST.Typ_exist
                      ([SailAST.KOpt_kind (SailAST.K_int, SailAST.Var k)], nc,
                        typ))
              -> Predicate.bind
                   (c_conv_i_i_o_o_o
                     ((SailAST.Var k,
                        (SailAST.K_int,
                          Syntax.CE_val
                            (Syntax.V_var (mk_x Arith.Zero_nat)))) ::
                       env)
                     nc)
                   (fun (_, (_, ca)) ->
                     Predicate.bind
                       (t_conv_raw_i_i_i_o_o_o_o
                         ((SailAST.Var k,
                            (SailAST.K_int,
                              Syntax.CE_val
                                (Syntax.V_var (mk_x Arith.Zero_nat)))) ::
                           env)
                         typ (Syntax.CE_val
                               (Syntax.V_var (mk_x Arith.Zero_nat))))
                       (fun (_, (_, (ba, caa))) ->
                         Predicate.single
                           (Syntax.T_refined_type
                             (mk_x Arith.Zero_nat, ba,
                               Syntax.C_conj (ca, caa)))))
            | (_, SailAST.Typ_exist
                    (SailAST.KOpt_kind (SailAST.K_int, SailAST.Var _) :: _ :: _,
                      _, _))
              -> Predicate.bot_pred
            | (_, SailAST.Typ_exist
                    (SailAST.KOpt_kind (SailAST.K_order, _) :: _, _, _))
              -> Predicate.bot_pred
            | (_, SailAST.Typ_exist
                    (SailAST.KOpt_kind (SailAST.K_bool, _) :: _, _, _))
              -> Predicate.bot_pred)));;

let rec add_to_pmctor
  x0 la pm_row = match x0, la, pm_row with [], la, pm_row -> [([pm_row], la)]
    | (pm, laa) :: pmlit, la, pm_row ->
        (if Option.equal_optiona
              (Product_Type.equal_prod (Lista.equal_list Stringa.equal_char)
                CodeGenPrelude.equal_x)
              laa la
          then (pm_row :: pm, la) :: pmlit
          else (pm, laa) :: add_to_pmctor pmlit la pm_row);;

let rec mk_fresh_many
  i1 x1 = match i1, x1 with i1, Arith.Zero_nat -> (i1, [])
    | i1, Arith.Suc v ->
        (let (i2, xa) = mk_fresh_x i1 in
         let (i3, xas) =
           mk_fresh_many i2 (Arith.minus_nat (Arith.Suc v) Arith.one_nat) in
          (i3, xa :: xas));;

let rec mk_tq_c_aux_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, []) -> Predicate.single Syntax.C_true
            | (_, _ :: _) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, []) -> Predicate.bot_pred
              | (m, SailAST.QI_id _ :: qis) ->
                Predicate.bind (mk_tq_c_aux_i_i_o m qis) Predicate.single
              | (_, SailAST.QI_constraint _ :: _) -> Predicate.bot_pred
              | (_, SailAST.QI_constant _ :: _) -> Predicate.bot_pred)))
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, []) -> Predicate.bot_pred
              | (_, SailAST.QI_id _ :: _) -> Predicate.bot_pred
              | (m, SailAST.QI_constraint nc :: qis) ->
                Predicate.bind (mk_tq_c_aux_i_i_o m qis)
                  (fun xb ->
                    Predicate.bind (c_conv_i_i_o_o_o m nc)
                      (fun (_, (_, c1)) ->
                        Predicate.single (Syntax.C_conj (c1, xb))))
              | (_, SailAST.QI_constant _ :: _) -> Predicate.bot_pred))));;

let rec mk_tq_c_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, SailAST.TypQ_tq _) -> Predicate.bot_pred
            | (_, SailAST.TypQ_no_forall) -> Predicate.single Syntax.C_true)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a
            with (m, SailAST.TypQ_tq qi_list) ->
              Predicate.bind (mk_tq_c_aux_i_i_o m qi_list) Predicate.single
            | (_, SailAST.TypQ_no_forall) -> Predicate.bot_pred)));;

let rec def_funtyp_i_i_o_o_o
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun a ->
        (match a with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
          | (_, SailAST.Typ_id _) -> Predicate.bot_pred
          | (_, SailAST.Typ_var _) -> Predicate.bot_pred
          | (tyq, SailAST.Typ_fn (in_typs, out_typ, _)) ->
            Predicate.bind
              (Predicate.if_pred
                (trace
                  ([Stringa.Chara
                      (false, false, true, false, false, true, true, false);
                     Stringa.Chara
                       (true, false, true, false, false, true, true, false);
                     Stringa.Chara
                       (false, true, true, false, false, true, true, false);
                     Stringa.Chara
                       (true, true, true, true, true, false, true, false);
                     Stringa.Chara
                       (false, true, true, false, false, true, true, false);
                     Stringa.Chara
                       (true, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (false, true, true, true, false, true, true, false);
                     Stringa.Chara
                       (false, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (true, false, false, true, true, true, true, false);
                     Stringa.Chara
                       (false, false, false, false, true, true, true, false);
                     Stringa.Chara
                       (false, false, false, false, false, true, false, false);
                     Stringa.Chara
                       (true, true, true, true, false, true, true, false);
                     Stringa.Chara
                       (true, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (false, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (true, true, true, true, true, false, true, false);
                     Stringa.Chara
                       (false, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (true, false, false, true, true, true, true, false);
                     Stringa.Chara
                       (false, false, false, false, true, true, true, false);
                     Stringa.Chara
                       (true, false, true, true, true, true, false, false)] @
                    ShowAST.shows_prec_typ Arith.Zero_nat out_typ [] @
                      Show.shows_prec_list ShowAST.show_typ Arith.Zero_nat
                        in_typs [])))
              (fun () ->
                Predicate.bind (eq_o_i (mk_tq_map tyq))
                  (fun xb ->
                    Predicate.bind
                      (eq_o_i
                        (Lista.map
                          (fun aa ->
                            (match aa
                              with (_, (SailAST.K_int, _)) -> AstUtils.int_typ
                              | (_, (SailAST.K_bool, _)) ->
                                AstUtils.bool_all_typ))
                          xb))
                      (fun xaa ->
                        Predicate.bind
                          (eq_o_i
                            (if Arith.equal_nat (Lista.size_list xaa)
                                  Arith.Zero_nat
                              then AstUtils.unit_typ
                              else (if Arith.equal_nat (Lista.size_list xaa)
 Arith.one_nat
                                     then Lista.hd xaa
                                     else SailAST.Typ_tup xaa)))
                          (fun xab ->
                            Predicate.bind (mk_tq_c_i_i_o xb tyq)
                              (fun xba ->
                                Predicate.bind (t_conv_i_i_o xb out_typ)
                                  (fun xc ->
                                    Predicate.bind
                                      (t_conv_raw_i_i_i_o_o_o_o xb xab
(Syntax.CE_fst (Syntax.CE_val (Syntax.V_var (mk_x Arith.one_nat)))))
                                      (fun (_, (_, (ba1, ca1))) ->
Predicate.bind
  (t_conv_raw_i_i_i_o_o_o_o xb (SailAST.Typ_tup in_typs)
    (Syntax.CE_snd (Syntax.CE_val (Syntax.V_var (mk_x Arith.one_nat)))))
  (fun (_, (_, (ba2, ca2))) ->
    Predicate.single
      (Syntax.B_pair (ba1, ba2),
        (Syntax.C_conj (xba, Syntax.C_conj (ca1, ca2)), xc))))))))))
          | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
          | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
          | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
          | (_, SailAST.Typ_exist (_, _, _)) -> Predicate.bot_pred));;

let rec variant_conv_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, []) -> Predicate.single []
            | (_, _ :: _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, []) -> Predicate.bot_pred
            | (env, SailAST.Tu_ty_id (typ, SailAST.Id ctor) :: tu_list) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    ([Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, false, true, true, false);
                       Stringa.Chara
                         (false, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, false, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, false, true,
                           false)] @
                      ShowAST.shows_prec_typ Arith.Zero_nat typ [])))
                (fun () ->
                  Predicate.bind (variant_conv_i_i_o env tu_list)
                    (fun xb ->
                      Predicate.bind (t_conv_i_i_o [] typ)
                        (fun xaa ->
                          Predicate.single
                            ((Stringa.explode ctor, xaa) :: xb))))
            | (_, SailAST.Tu_ty_id (_, SailAST.Operator _) :: _) ->
              Predicate.bot_pred)));;

let rec expand_ctor_i_i_i_i_i_o_o_o
  x xb xc xd xe =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
        (fun a ->
          (match a with (_, (_, ([], _))) -> Predicate.bot_pred
            | (_, (_, (([], _) :: _, _))) -> Predicate.bot_pred
            | (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (n1, (env, ((SailAST.P_app (_, ctor, pats) :: pm_pat, sa) :: pm,
                           (tyid, xa))))
              -> Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (eq_o_i ctor)
                       (fun aa ->
                         (match aa
                           with SailAST.Id dc ->
                             Predicate.bind
                               (expand_ctor_i_i_i_i_i_o_o_o n1 env pm tyid xa)
                               (fun (pmctor, (ms, n2)) ->
                                 Predicate.bind
                                   (Predicate.if_pred
                                     (trace
                                       ([Stringa.Chara
   (true, false, true, false, false, true, true, false);
  Stringa.Chara (false, false, false, true, true, true, true, false);
  Stringa.Chara (false, false, false, false, true, true, true, false);
  Stringa.Chara (true, false, false, false, false, true, true, false);
  Stringa.Chara (false, true, true, true, false, true, true, false);
  Stringa.Chara (false, false, true, false, false, true, true, false);
  Stringa.Chara (true, true, true, true, true, false, true, false);
  Stringa.Chara (true, true, false, false, false, true, true, false);
  Stringa.Chara (false, false, true, false, true, true, true, false);
  Stringa.Chara (true, true, true, true, false, true, true, false);
  Stringa.Chara (false, true, false, false, true, true, true, false);
  Stringa.Chara (true, false, false, true, false, false, true, false);
  Stringa.Chara (false, false, false, false, false, true, false, false);
  Stringa.Chara (true, false, false, true, false, true, true, false);
  Stringa.Chara (false, true, false, false, true, true, false, false);
  Stringa.Chara (true, false, true, true, true, true, false, false)] @
 Show_Instances.shows_prec_nat Arith.Zero_nat n2 [])))
                                   (fun () ->
                                     Predicate.single
                                       (add_to_pmctor pmctor
  (Some (Stringa.explode dc, mk_x Arith.Zero_nat)) (pats @ pm_pat, sa),
 (ms, n2))))
                           | SailAST.Operator _ -> Predicate.bot_pred)))
            | (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred
            | (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _))) ->
              Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
          (fun a ->
            (match a with (_, (_, ([], _))) -> Predicate.bot_pred
              | (_, (_, (([], _) :: _, _))) -> Predicate.bot_pred
              | (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (n1, (_, ((SailAST.P_wild _ :: pm_pat, sa) :: _, (_, _)))) ->
                Predicate.single ([([(pm_pat, sa)], None)], ([], n1))
              | (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred
              | (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _))) ->
                Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
            (fun a ->
              (match a with (_, (_, ([], _))) -> Predicate.bot_pred
                | (_, (_, (([], _) :: _, _))) -> Predicate.bot_pred
                | (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (n1, (env, ((SailAST.P_id (_, idd) :: pm_pat, sa) :: _,
                               (_, _))))
                  -> Predicate.bind
                       (Predicate.if_pred
                         (trace
                           [Stringa.Chara
                              (true, false, true, false, false, true, true,
                                false);
                             Stringa.Chara
                               (false, false, false, true, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (true, true, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, false, true,
                                 false)]))
                       (fun () ->
                         Predicate.bind
                           (eq_i_i (Option.equal_option SailAST.equal_typ) None
                             (Env.lookup_enum_env env idd))
                           (fun () ->
                             Predicate.single
                               ([([(pm_pat, sa)], None)], ([], n1))))
                | (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _)))
                  -> Predicate.bot_pred
                | (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _))) ->
                  Predicate.bot_pred
                | (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _)))
                  -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
              (fun a ->
                (match a with (_, (_, ([], _))) -> Predicate.bot_pred
                  | (_, (_, (([], _) :: _, _))) -> Predicate.bot_pred
                  | (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (n1, (env, ((SailAST.P_id (_, SailAST.Id dc) :: pm_pat,
                                  sa) ::
                                  pm,
                                 (tyid, xa))))
                    -> Predicate.bind
                         (Predicate.if_pred
                           (trace
                             [Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (false, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false)]))
                         (fun () ->
                           Predicate.bind
                             (eq_o_i (Env.lookup_enum_env env (SailAST.Id dc)))
                             (fun aa ->
                               (match aa with None -> Predicate.bot_pred
                                 | Some _ ->
                                   Predicate.bind
                                     (expand_ctor_i_i_i_i_i_o_o_o n1 env pm tyid
                                       xa)
                                     (fun (pmctor, (ms, n2)) ->
                                       Predicate.bind
 (Predicate.if_pred
   (trace
     ([Stringa.Chara (true, false, true, false, false, true, true, false);
        Stringa.Chara (false, false, false, true, true, true, true, false);
        Stringa.Chara (false, false, false, false, true, true, true, false);
        Stringa.Chara (true, false, false, false, false, true, true, false);
        Stringa.Chara (false, true, true, true, false, true, true, false);
        Stringa.Chara (false, false, true, false, false, true, true, false);
        Stringa.Chara (true, true, true, true, true, false, true, false);
        Stringa.Chara (true, false, true, false, false, true, true, false);
        Stringa.Chara (false, true, true, true, false, true, true, false);
        Stringa.Chara (true, false, true, false, true, true, true, false);
        Stringa.Chara (true, false, true, true, false, true, true, false);
        Stringa.Chara (true, false, false, true, false, false, true, false);
        Stringa.Chara (false, false, false, false, false, true, false, false);
        Stringa.Chara (true, false, false, true, false, true, true, false);
        Stringa.Chara (false, true, false, false, true, true, false, false);
        Stringa.Chara (true, false, true, true, true, true, false, false)] @
       Show_Instances.shows_prec_nat Arith.Zero_nat n2 [])))
 (fun () ->
   Predicate.single
     (add_to_pmctor pmctor (Some (Stringa.explode dc, mk_x Arith.Zero_nat))
        (SailAST.P_lit (None, SailAST.L_unit) :: pm_pat, sa),
       (ms, n2)))))))
                  | (_, (_, ((SailAST.P_id (_, SailAST.Operator _) :: _, _) ::
                               _,
                              _)))
                    -> Predicate.bot_pred
                  | (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _)))
                    -> Predicate.bot_pred
                  | (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _)))
                    -> Predicate.bot_pred)))
            (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
              (fun a ->
                (match a
                  with (n1, (_, ([], (_, _)))) ->
                    Predicate.single ([], ([], n1))
                  | (_, (_, (_ :: _, _))) -> Predicate.bot_pred))))));;

let rec fresh_vars_list
  i x1 = match i, x1 with i, Arith.Zero_nat -> (i, [])
    | i, Arith.Suc v ->
        (let (i2, xalist) =
           fresh_vars_list (Arith.plus_nat i Arith.one_nat)
             (Arith.minus_nat (Arith.Suc v) Arith.one_nat)
           in
          (i2, mk_x i :: xalist));;

let rec expand_tuple_i_i_i_i_o_o_o
  x xb xc xd =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a
            with (i1, ([], (_, _))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, true, true, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () -> Predicate.single ([], ([], i1)))
            | (_, (_ :: _, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
          (fun a ->
            (match a with (_, ([], _)) -> Predicate.bot_pred
              | (_, (([], _) :: _, _)) -> Predicate.bot_pred
              | (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_wild _ :: _, _) :: _, _)) -> Predicate.bot_pred
              | (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (i1, ((SailAST.P_tup (_, pats) :: pm_pat, sa) :: pm,
                       (num_ele, xa)))
                -> Predicate.bind
                     (Predicate.if_pred
                       (trace
                         [Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                           Stringa.Chara
                             (false, false, false, true, true, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, true, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (false, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (false, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, false, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, false, true, false,
                               false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, true, true, true, false,
                               false)]))
                     (fun () ->
                       Predicate.bind (eq_o_i (fresh_vars_list i1 num_ele))
                         (fun (i2, _) ->
                           Predicate.bind
                             (Predicate.if_pred
                               (trace
                                 ([Stringa.Chara
                                     (true, false, true, false, false, true,
                                       true, false);
                                    Stringa.Chara
                                      (false, false, false, true, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, false, false, false, true,
true, false);
                                    Stringa.Chara
                                      (false, true, true, true, false, true,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, true, true, true, false,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, true, true, false, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, true, true, true, false,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, false, true, false, false,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, false, true,
false, false);
                                    Stringa.Chara
                                      (true, false, false, true, false, true,
true, false);
                                    Stringa.Chara
                                      (false, true, false, false, true, true,
false, false);
                                    Stringa.Chara
                                      (true, false, true, true, true, true,
false, false)] @
                                   Show_Instances.shows_prec_nat Arith.Zero_nat
                                     i2 [])))
                             (fun () ->
                               Predicate.bind
                                 (expand_tuple_i_i_i_i_o_o_o i2 pm num_ele xa)
                                 (fun (pma, (xalist, i3)) ->
                                   Predicate.bind
                                     (Predicate.if_pred
                                       (trace
 ([Stringa.Chara (true, false, true, false, false, true, true, false);
    Stringa.Chara (false, false, false, true, true, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (true, false, false, false, false, true, true, false);
    Stringa.Chara (false, true, true, true, false, true, true, false);
    Stringa.Chara (false, false, true, false, false, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, false, true, false, true, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (false, false, true, true, false, true, true, false);
    Stringa.Chara (true, false, true, false, false, true, true, false);
    Stringa.Chara (true, true, true, true, true, false, true, false);
    Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, false, true, false, true, true, true, false);
    Stringa.Chara (false, false, false, false, true, true, true, false);
    Stringa.Chara (true, false, false, true, false, false, true, false);
    Stringa.Chara (false, false, false, false, false, true, false, false);
    Stringa.Chara (true, false, false, true, false, true, true, false);
    Stringa.Chara (true, true, false, false, true, true, false, false);
    Stringa.Chara (true, false, true, true, true, true, false, false)] @
   Show_Instances.shows_prec_nat Arith.Zero_nat i3 [])))
                                     (fun () ->
                                       Predicate.single
 ((pats @ pm_pat, sa) :: pma, (xalist, i3)))))))
              | (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred
              | (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _)) ->
                Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
            (fun a ->
              (match a with (_, ([], _)) -> Predicate.bot_pred
                | (_, (([], _) :: _, _)) -> Predicate.bot_pred
                | (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (i1, ((SailAST.P_wild lc :: pm_pat, sa) :: _, (num_ele, _)))
                  -> Predicate.bind (eq_o_i (fresh_vars_list i1 num_ele))
                       (fun (_, xalist) ->
                         Predicate.single
                           ([(Lista.map (fun _ -> SailAST.P_wild lc) xalist @
                                pm_pat,
                               sa)],
                             (xalist, i1)))
                | (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred)))
          (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
            (fun a ->
              (match a with (_, ([], _)) -> Predicate.bot_pred
                | (_, (([], _) :: _, _)) -> Predicate.bot_pred
                | (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_wild _ :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (i1, ((SailAST.P_id (lc, _) :: pm_pat, sa) :: _,
                         (num_ele, _)))
                  -> Predicate.bind
                       (Predicate.if_pred
                         (trace
                           [Stringa.Chara
                              (true, false, true, false, false, true, true,
                                false);
                             Stringa.Chara
                               (false, false, false, true, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, true, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, false, true,
                                 false)]))
                       (fun () ->
                         Predicate.bind (eq_o_i (fresh_vars_list i1 num_ele))
                           (fun (i1a, xalist) ->
                             (if Arith.equal_nat i1 i1a
                               then Predicate.single
                                      ([(Lista.map (fun _ -> SailAST.P_wild lc)
   xalist @
   pm_pat,
  sa)],
(xalist, i1))
                               else Predicate.bot_pred)))
                | (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred
                | (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _)) ->
                  Predicate.bot_pred)))));;

let rec expand_vector_concat_i_i_i_i_o_o_o
  x xc xd xe =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xc, (xd, xe))))
        (fun a ->
          (match a
            with (i1, (_, (xb, []))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, true, true, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, true, true, true, false)]))
                (fun () -> Predicate.single (L_hole, (xb, i1)))
            | (_, (_, (_, _ :: _))) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xc, (xd, xe))))
          (fun a ->
            (match a with (_, (_, (_, []))) -> Predicate.bot_pred
              | (i1, (xa, (xb, SailAST.P_lit (_, lit) :: ps))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      [Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true,
                            false)]))
                  (fun () ->
                    Predicate.bind (eq_o_i (mk_fresh_x i1))
                      (fun (i2, xb1) ->
                        Predicate.bind (eq_o_i (mk_fresh_x i2))
                          (fun (i3, xaa) ->
                            Predicate.bind (eq_o_i (mk_fresh_x i3))
                              (fun (i4, xa1) ->
                                Predicate.bind (eq_o_i (mk_fresh_x i4))
                                  (fun (i5, xa2) ->
                                    Predicate.bind
                                      (Predicate.if_pred
(trace
  ([Stringa.Chara (true, false, true, false, false, true, true, false);
     Stringa.Chara (false, false, false, true, true, true, true, false);
     Stringa.Chara (false, false, false, false, true, true, true, false);
     Stringa.Chara (true, false, false, false, false, true, true, false);
     Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (false, false, true, false, false, true, true, false);
     Stringa.Chara (true, true, true, true, true, false, true, false);
     Stringa.Chara (false, true, true, false, true, true, true, false);
     Stringa.Chara (true, true, false, false, false, true, true, false);
     Stringa.Chara (true, true, true, true, true, false, true, false);
     Stringa.Chara (false, false, true, true, false, true, true, false);
     Stringa.Chara (true, false, false, true, false, true, true, false);
     Stringa.Chara (false, false, true, false, true, true, true, false);
     Stringa.Chara (true, false, false, true, false, false, true, false);
     Stringa.Chara (false, false, false, false, false, true, false, false);
     Stringa.Chara (true, false, false, true, false, true, true, false);
     Stringa.Chara (true, false, true, false, true, true, false, false);
     Stringa.Chara (true, false, true, true, true, true, false, false)] @
    Show_Instances.shows_prec_nat Arith.Zero_nat i5 [])))
                                      (fun () ->
Predicate.bind (lit_conv_i_o lit)
  (fun xf ->
    Predicate.bind (eq_o_i (get_len_lit lit))
      (fun xca ->
        Predicate.bind
          (eq_o_i
            (L_let
              (xaa, Syntax.AE_split (Syntax.V_var xa, xca),
                L_let (xa1, Syntax.AE_fst (Syntax.V_var xaa),
                        L_let (xa2, Syntax.AE_snd (Syntax.V_var xaa),
                                L_hole)))))
          (fun xab ->
            Predicate.bind
              (eq_o_i
                (L_let
                  (xb1, Syntax.AE_app
                          ([Stringa.Chara
                              (true, false, true, false, false, true, true,
                                false);
                             Stringa.Chara
                               (true, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false)],
                            Syntax.V_pair
                              (Syntax.V_var xb,
                                Syntax.V_pair
                                  (Syntax.V_var xa1, Syntax.V_lit xf))),
                    L_hole)))
              (fun xg ->
                Predicate.bind
                  (expand_vector_concat_i_i_i_i_o_o_o i5 xa2 xb1 ps)
                  (fun (l3, (xb2, i6)) ->
                    Predicate.bind
                      (Predicate.if_pred
                        (trace
                          ([Stringa.Chara
                              (true, false, true, false, false, true, true,
                                false);
                             Stringa.Chara
                               (false, false, false, true, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, false, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, false, true, false,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, false, true, true, false,
                                 false);
                             Stringa.Chara
                               (true, false, true, true, true, true, false,
                                 false)] @
                            Show_Instances.shows_prec_nat Arith.Zero_nat i6
                              [])))
                      (fun () ->
                        Predicate.single
                          (L_compose (L_compose (xab, xg), l3),
                            (xb2, i6))))))))))))))
              | (_, (_, (_, SailAST.P_wild _ :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_or (_, _, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_not (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_as (_, _, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_id (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_var (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_app (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_vector (_, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_vector_concat (_, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_tup (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_list (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_cons (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_string_append (_, _) :: _))) ->
                Predicate.bot_pred)))
        (Predicate.bind (Predicate.single (x, (xc, (xd, xe))))
          (fun a ->
            (match a with (_, (_, (_, []))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_lit (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_wild _ :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_or (_, _, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_not (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_as (_, _, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_lit (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_wild _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_or (_, _, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_not (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_as (_, _, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_typ (_, _, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (i1, (xa, (xb, SailAST.P_typ (_, typ, SailAST.P_id (_, _)) ::
                                 ps)))
                -> Predicate.bind
                     (Predicate.if_pred
                       (trace
                         ([Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                            Stringa.Chara
                              (false, false, false, true, true, true, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, true, true, false, true, true,
                                false);
                            Stringa.Chara
                              (false, false, true, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, true, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, false, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, false, true, false,
                                false);
                            Stringa.Chara
                              (false, false, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, true, true, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, true, true, true, true, false,
                                false)] @
                           ShowAST.shows_prec_typ Arith.Zero_nat typ [])))
                     (fun () ->
                       Predicate.bind (eq_o_i (mk_fresh_x i1))
                         (fun (i2, _) ->
                           Predicate.bind (eq_o_i (mk_fresh_x i2))
                             (fun (i3, xaa) ->
                               Predicate.bind (eq_o_i (mk_fresh_x i3))
                                 (fun (i4, xa1) ->
                                   Predicate.bind (eq_o_i (mk_fresh_x i4))
                                     (fun (i5, xa2) ->
                                       Predicate.bind (eq_o_i (mk_fresh_x i5))
 (fun (i6, xa_id) ->
   Predicate.bind (get_len_i_o typ)
     (fun xf ->
       Predicate.bind
         (eq_o_i
           (L_let
             (xaa, Syntax.AE_split (Syntax.V_var xa, xf),
               L_let (xa1, Syntax.AE_fst (Syntax.V_var xaa),
                       L_let (xa2, Syntax.AE_snd (Syntax.V_var xaa), L_hole)))))
         (fun xg ->
           Predicate.bind
             (eq_o_i (L_let (xa_id, Syntax.AE_val (Syntax.V_var xa1), L_hole)))
             (fun xab ->
               Predicate.bind (expand_vector_concat_i_i_i_i_o_o_o i6 xa2 xb ps)
                 (fun (l3, (xb2, i7)) ->
                   Predicate.bind
                     (Predicate.if_pred
                       (trace
                         ([Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                            Stringa.Chara
                              (false, false, false, true, true, true, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, true, true, false, true, true,
                                false);
                            Stringa.Chara
                              (false, false, true, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, true, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, true, true, false, true,
                                false);
                            Stringa.Chara
                              (false, true, true, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, false, false, true, true,
                                false);
                            Stringa.Chara
                              (false, true, false, false, true, true, true,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, false, true,
                                false);
                            Stringa.Chara
                              (false, false, false, false, false, true, false,
                                false);
                            Stringa.Chara
                              (true, false, false, true, false, true, true,
                                false);
                            Stringa.Chara
                              (true, true, true, false, true, true, false,
                                false);
                            Stringa.Chara
                              (true, false, true, true, true, true, false,
                                false)] @
                           Show_Instances.shows_prec_nat Arith.Zero_nat i7 [])))
                     (fun () ->
                       Predicate.single
                         (L_compose (L_compose (xg, xab), l3),
                           (xb2, i7)))))))))))))
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_var (_, _, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_app (_, _, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_vector (_, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ
                              (_, _, SailAST.P_vector_concat (_, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_tup (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_list (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ (_, _, SailAST.P_cons (_, _, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_typ
                              (_, _, SailAST.P_string_append (_, _)) ::
                              _)))
                -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_id (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_var (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_app (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_vector (_, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_vector_concat (_, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_tup (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_list (_, _) :: _))) -> Predicate.bot_pred
              | (_, (_, (_, SailAST.P_cons (_, _, _) :: _))) ->
                Predicate.bot_pred
              | (_, (_, (_, SailAST.P_string_append (_, _) :: _))) ->
                Predicate.bot_pred))));;

let rec expand_lit_i_i_i_i_i_o_o_o
  x xc xd xe xf =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
        (fun a ->
          (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
            | (_, (_, (_, (([], _) :: _, _)))) -> Predicate.bot_pred
            | (i1, (env, (xmap,
                           ((SailAST.P_lit (_, lit) :: pm_pat, sa) :: pm, xp))))
              -> Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (lit_conv_i_o lit)
                       (fun xa ->
                         Predicate.bind
                           (expand_lit_i_i_i_i_i_o_o_o i1 env xmap pm xp)
                           (fun (pmlit, (ms, i2)) ->
                             Predicate.bind
                               (Predicate.if_pred
                                 (trace
                                   ([Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                      Stringa.Chara
(false, false, false, true, true, true, true, false);
                                      Stringa.Chara
(false, false, false, false, true, true, true, false);
                                      Stringa.Chara
(true, false, false, false, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, false, true, false, false, true, true, false);
                                      Stringa.Chara
(true, true, true, true, true, false, true, false);
                                      Stringa.Chara
(false, false, true, true, false, true, true, false);
                                      Stringa.Chara
(true, false, false, true, false, true, true, false);
                                      Stringa.Chara
(false, false, true, false, true, true, true, false);
                                      Stringa.Chara
(true, true, true, true, true, false, true, false);
                                      Stringa.Chara
(false, false, true, true, false, true, true, false);
                                      Stringa.Chara
(true, false, false, true, false, true, true, false);
                                      Stringa.Chara
(false, false, true, false, true, true, true, false);
                                      Stringa.Chara
(true, false, false, true, false, false, true, false);
                                      Stringa.Chara
(false, false, false, false, false, true, false, false);
                                      Stringa.Chara
(true, false, false, true, false, true, true, false);
                                      Stringa.Chara
(false, true, false, false, true, true, false, false);
                                      Stringa.Chara
(false, false, false, false, false, true, false, false);
                                      Stringa.Chara
(true, false, true, true, true, true, false, false);
                                      Stringa.Chara
(false, false, false, false, false, true, false, false)] @
                                     Show_Instances.shows_prec_nat
                                       Arith.Zero_nat i2 [])))
                               (fun () ->
                                 Predicate.bind (eq_o_i (mk_fresh_x i2))
                                   (fun (i3, xb) ->
                                     Predicate.bind
                                       (Predicate.if_pred
 (trace
   ([Stringa.Chara (true, false, true, false, false, true, true, false);
      Stringa.Chara (false, false, false, true, true, true, true, false);
      Stringa.Chara (false, false, false, false, true, true, true, false);
      Stringa.Chara (true, false, false, false, false, true, true, false);
      Stringa.Chara (false, true, true, true, false, true, true, false);
      Stringa.Chara (false, false, true, false, false, true, true, false);
      Stringa.Chara (true, true, true, true, true, false, true, false);
      Stringa.Chara (false, false, true, true, false, true, true, false);
      Stringa.Chara (true, false, false, true, false, true, true, false);
      Stringa.Chara (false, false, true, false, true, true, true, false);
      Stringa.Chara (true, true, true, true, true, false, true, false);
      Stringa.Chara (false, false, true, true, false, true, true, false);
      Stringa.Chara (true, false, false, true, false, true, true, false);
      Stringa.Chara (false, false, true, false, true, true, true, false);
      Stringa.Chara (true, false, false, true, false, false, true, false);
      Stringa.Chara (false, false, false, false, false, true, false, false);
      Stringa.Chara (true, false, false, true, false, true, true, false);
      Stringa.Chara (true, true, false, false, true, true, false, false);
      Stringa.Chara (false, false, false, false, false, true, false, false);
      Stringa.Chara (true, false, true, true, true, true, false, false);
      Stringa.Chara (false, false, false, false, false, true, false, false)] @
     Show_Instances.shows_prec_nat Arith.Zero_nat i3 [])))
                                       (fun () ->
 Predicate.bind
   (eq_o_i
     (L_let
       (xb, Syntax.AE_app
              ([Stringa.Chara
                  (true, false, true, false, false, true, true, false);
                 Stringa.Chara
                   (true, false, false, false, true, true, true, false)],
                Syntax.V_pair (Syntax.V_var xp, Syntax.V_lit xa)),
         L_hole)))
   (fun xg ->
     Predicate.single
       (([(pm_pat, sa)], Some (xg, xb)) :: pmlit, (ms, i3)))))))))
            | (_, (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _, _))))
              -> Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _, _))))
              -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
              | (_, (_, (_, (([], _) :: _, _)))) -> Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (i1, (_, (_, ((SailAST.P_wild _ :: pm_pat, sa) :: _, _)))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      [Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, false, true,
                            false)]))
                  (fun () ->
                    Predicate.single ([([(pm_pat, sa)], None)], ([], i1)))
              | (_, (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _,
                              _))))
                -> Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)))) ->
                Predicate.bot_pred
              | (_, (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _,
                              _))))
                -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
                | (_, (_, (_, (([], _) :: _, _)))) -> Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (i1, (_, (xmap,
                             ((SailAST.P_id (_, idd) :: pm_pat, sa) :: _, xp))))
                  -> Predicate.bind
                       (Predicate.if_pred
                         (trace
                           [Stringa.Chara
                              (true, false, true, false, false, true, true,
                                false);
                             Stringa.Chara
                               (false, false, false, true, true, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, false, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, true, true, true, true, false, true,
                                 false);
                             Stringa.Chara
                               (false, true, true, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, false, false, true, true,
                                 false);
                             Stringa.Chara
                               (false, true, false, false, true, true, true,
                                 false);
                             Stringa.Chara
                               (true, false, false, true, false, false, true,
                                 false)]))
                       (fun () ->
                         Predicate.bind
                           (eq_o_i (Env.lookup SailAST.equal_id xmap idd))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some xa ->
                                 Predicate.single
                                   ([([(pm_pat,
 Syntax.AS_let (xa, Syntax.AE_val (Syntax.V_var xp), sa))],
                                       None)],
                                     ([(idd, xa)], i1)))))
                | (_, (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _,
                                _))))
                  -> Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _,
                                _))))
                  -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
              (fun a ->
                (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
                  | (_, (_, (_, (([], _) :: _, _)))) -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (i1, (env, (xmap,
                                 ((SailAST.P_typ (_, _, pat) :: pm_pat, sa) ::
                                    pm,
                                   xp))))
                    -> Predicate.bind
                         (Predicate.if_pred
                           (trace
                             [Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (false, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false)]))
                         (fun () ->
                           Predicate.bind
                             (expand_lit_i_i_i_i_i_o_o_o i1 env xmap
                               ((pat :: pm_pat, sa) :: pm) xp)
                             (fun (pma, (ids, i2)) ->
                               Predicate.single (pma, (ids, i2))))
                  | (_, (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))))
                    -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _))))
                    -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))))
                    -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_vector_concat (_, _) :: _, _) :: _,
                                  _))))
                    -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _)))) ->
                    Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _, _))))
                    -> Predicate.bot_pred
                  | (_, (_, (_, ((SailAST.P_string_append (_, _) :: _, _) :: _,
                                  _))))
                    -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
                (fun a ->
                  (match a
                    with (i1, (_, (_, ([], _)))) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            [Stringa.Chara
                               (true, false, true, false, false, true, true,
                                 false);
                              Stringa.Chara
                                (false, false, false, true, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, false, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, true, true, true, false, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, false, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, true, true, true, false, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, false, true, true, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, false, true, false, false, true,
                                  false)]))
                        (fun () -> Predicate.single ([], ([], i1)))
                    | (_, (_, (_, (_ :: _, _)))) -> Predicate.bot_pred)))
              (Predicate.bind (Predicate.single (x, (xc, (xd, (xe, xf)))))
                (fun a ->
                  (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
                    | (_, (_, (_, (([], _) :: _, _)))) -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_lit (_, _) :: _, _) :: _, _)))) ->
                      Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_wild _ :: _, _) :: _, _)))) ->
                      Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_or (_, _, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_not (_, _) :: _, _) :: _, _)))) ->
                      Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_as (_, _, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_typ (_, _, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_id (_, _) :: _, _) :: _, _)))) ->
                      Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_var (_, _, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_app (_, _, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_vector (_, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (i1, (env, (xmap,
                                   ((SailAST.P_vector_concat (_, pats) ::
                                       pm_pat,
                                      sa) ::
                                      pm,
                                     xp))))
                      -> Predicate.bind
                           (Predicate.if_pred
                             (trace
                               [Stringa.Chara
                                  (true, false, true, false, false, true, true,
                                    false);
                                 Stringa.Chara
                                   (false, false, false, true, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, false, false, true, true,
                                     true, false);
                                 Stringa.Chara
                                   (true, false, false, false, false, true,
                                     true, false);
                                 Stringa.Chara
                                   (false, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, false, false, true,
                                     true, false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, false, false, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, false, false, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, false, false, true,
                                     true, false);
                                 Stringa.Chara
                                   (false, false, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, false,
                                     true, false)]))
                           (fun () ->
                             Predicate.bind (eq_o_i (mk_fresh_x i1))
                               (fun (i2, xb) ->
                                 Predicate.bind
                                   (Predicate.if_pred
                                     (trace
                                       ([Stringa.Chara
   (true, false, true, false, false, true, true, false);
  Stringa.Chara (false, false, false, true, true, true, true, false);
  Stringa.Chara (false, false, false, false, true, true, true, false);
  Stringa.Chara (true, false, false, false, false, true, true, false);
  Stringa.Chara (false, true, true, true, false, true, true, false);
  Stringa.Chara (false, false, true, false, false, true, true, false);
  Stringa.Chara (true, true, true, true, true, false, true, false);
  Stringa.Chara (false, false, true, true, false, true, true, false);
  Stringa.Chara (true, false, false, true, false, true, true, false);
  Stringa.Chara (false, false, true, false, true, true, true, false);
  Stringa.Chara (true, true, true, true, true, false, true, false);
  Stringa.Chara (true, true, false, false, false, true, true, false);
  Stringa.Chara (true, true, true, true, false, true, true, false);
  Stringa.Chara (false, true, true, true, false, true, true, false);
  Stringa.Chara (true, true, false, false, false, true, true, false);
  Stringa.Chara (true, false, false, false, false, true, true, false);
  Stringa.Chara (false, false, true, false, true, true, true, false);
  Stringa.Chara (true, false, false, true, false, false, true, false);
  Stringa.Chara (false, false, false, false, false, true, false, false);
  Stringa.Chara (true, false, false, true, false, true, true, false);
  Stringa.Chara (false, true, false, false, true, true, false, false);
  Stringa.Chara (true, false, true, true, true, true, false, false)] @
 Show_Instances.shows_prec_nat Arith.Zero_nat i2 [])))
                                   (fun () ->
                                     Predicate.bind
                                       (expand_vector_concat_i_i_i_i_o_o_o i2 xp
 xb pats)
                                       (fun (l, (xb2, i3)) ->
 Predicate.bind
   (Predicate.if_pred
     (trace
       ([Stringa.Chara (true, false, true, false, false, true, true, false);
          Stringa.Chara (false, false, false, true, true, true, true, false);
          Stringa.Chara (false, false, false, false, true, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (false, false, true, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, false, true, true, false, true, true, false);
          Stringa.Chara (true, false, false, true, false, true, true, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, false, false, true, false, false, true, false);
          Stringa.Chara (false, false, false, false, false, true, false, false);
          Stringa.Chara (true, false, false, true, false, true, true, false);
          Stringa.Chara (true, true, false, false, true, true, false, false);
          Stringa.Chara (true, false, true, true, true, true, false, false)] @
         Show_Instances.shows_prec_nat Arith.Zero_nat i3 [])))
   (fun () ->
     Predicate.bind (expand_lit_i_i_i_i_i_o_o_o i3 env xmap pm xp)
       (fun (pmlist, (ms, i4)) ->
         Predicate.bind
           (Predicate.if_pred
             (trace
               ([Stringa.Chara
                   (true, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (false, false, false, true, true, true, true, false);
                  Stringa.Chara
                    (false, false, false, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, true, false, true, false);
                  Stringa.Chara
                    (false, false, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, true, false, true, false);
                  Stringa.Chara
                    (true, true, false, false, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, false, true, true, false);
                  Stringa.Chara
                    (true, false, false, false, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false);
                  Stringa.Chara
                    (true, false, false, true, false, false, true, false);
                  Stringa.Chara
                    (false, false, false, false, false, true, false, false);
                  Stringa.Chara
                    (true, false, false, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, false, false, true, true, false, false);
                  Stringa.Chara
                    (true, false, true, true, true, true, false, false)] @
                 Show_Instances.shows_prec_nat Arith.Zero_nat i4 [])))
           (fun () ->
             Predicate.single
               (([(pm_pat, sa)], Some (l, xb2)) :: pmlist, (ms, i4)))))))))
                    | (_, (_, (_, ((SailAST.P_tup (_, _) :: _, _) :: _, _)))) ->
                      Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_list (_, _) :: _, _) :: _, _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_cons (_, _, _) :: _, _) :: _,
                                    _))))
                      -> Predicate.bot_pred
                    | (_, (_, (_, ((SailAST.P_string_append (_, _) :: _, _) ::
                                     _,
                                    _))))
                      -> Predicate.bot_pred)))))));;

let rec as_unpack_i_i_i_i_o_o
  x xb xc xd =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a with (i, (_, ([], sa))) -> Predicate.single (sa, i)
            | (_, (_, (_ :: _, _))) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a with (_, (_, ([], _))) -> Predicate.bot_pred
            | (i1, (xa1, (xa2 :: xas, sa))) ->
              Predicate.bind (eq_o_i (mk_fresh_x i1))
                (fun (i2, xa) ->
                  Predicate.bind (as_unpack_i_i_i_i_o_o i2 xa xas sa)
                    (fun (saa, i3) ->
                      Predicate.single
                        (Syntax.AS_let
                           (xa2, Syntax.AE_fst (Syntax.V_var xa1),
                             Syntax.AS_let
                               (xa, Syntax.AE_snd (Syntax.V_var xa1), saa)),
                          i3))))));;

let rec is_literal_base
  = function
    SailAST.Typ_id (SailAST.Id tyid) ->
      Set.member Stringa.equal_literal tyid
        (Set.insert Stringa.equal_literal "bool"
          (Set.insert Stringa.equal_literal "int"
            (Set.insert Stringa.equal_literal "unit" Set.bot_set)))
    | SailAST.Typ_app (SailAST.Id tyid, uu) ->
        Set.member Stringa.equal_literal tyid
          (Set.insert Stringa.equal_literal "bool"
            (Set.insert Stringa.equal_literal "int"
              (Set.insert Stringa.equal_literal "atom_bool"
                (Set.insert Stringa.equal_literal "atom"
                  (Set.insert Stringa.equal_literal "vector"
                    (Set.insert Stringa.equal_literal "bitvector"
                      Set.bot_set))))))
    | SailAST.Typ_internal_unknown -> false
    | SailAST.Typ_id (SailAST.Operator va) -> false
    | SailAST.Typ_var v -> false
    | SailAST.Typ_fn (v, va, vb) -> false
    | SailAST.Typ_bidir (v, va, vb) -> false
    | SailAST.Typ_tup v -> false
    | SailAST.Typ_app (SailAST.Operator vb, va) -> false
    | SailAST.Typ_exist (v, va, vb) -> false;;

let rec conv_pattern_matrix_i_i_i_i_i_o_o
  x xb xc xd xe =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
        (fun a ->
          (match a with (_, (_, (_, (_, [])))) -> Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_internal_unknown, _) :: _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_id _, _) :: _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_var _, _) :: _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_fn (_, _, _), _) :: _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_bidir (_, _, _), _) :: _)))) ->
              Predicate.bot_pred
            | (i1, (env, (xmap, (pm, (SailAST.Typ_tup bs, xa) :: bss)))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () ->
                  Predicate.bind
                    (eq_o_i (mk_fresh_many i1 (Lista.size_list bs)))
                    (fun (i2, xas) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Show_Instances.shows_prec_nat Arith.Zero_nat i2
                                [])))
                        (fun () ->
                          Predicate.bind
                            (expand_tuple_i_i_i_i_o_o_o i2 pm
                              (Lista.size_list bs) xa)
                            (fun (pma, (xalist, i3)) ->
                              Predicate.bind
                                (Predicate.if_pred
                                  (trace
                                    ([Stringa.Chara
(true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, false, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, true, false, true, true, true, false);
                                       Stringa.Chara
 (false, false, false, false, true, true, true, false);
                                       Stringa.Chara
 (false, false, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, false, true, false, false, true, true, false);
                                       Stringa.Chara
 (true, false, false, true, false, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, false, true, false, false);
                                       Stringa.Chara
 (true, false, false, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, false, true, true, false, false);
                                       Stringa.Chara
 (true, false, true, true, true, true, false, false)] @
                                      Show_Instances.shows_prec_nat
Arith.Zero_nat i3 [] @
Show.shows_prec_list ShowAST.show_typ Arith.Zero_nat bs [])))
                                (fun () ->
                                  Predicate.bind
                                    (conv_pattern_matrix_i_i_i_i_i_o_o i3 env
                                      xmap pma (Lista.zip bs xas @ bss))
                                    (fun (sa, i4) ->
                                      Predicate.bind
(Predicate.if_pred
  (trace
    ([Stringa.Chara (true, true, false, false, false, true, true, false);
       Stringa.Chara (true, true, true, true, false, true, true, false);
       Stringa.Chara (false, true, true, true, false, true, true, false);
       Stringa.Chara (false, true, true, false, true, true, true, false);
       Stringa.Chara (true, true, true, true, true, false, true, false);
       Stringa.Chara (false, false, false, false, true, true, true, false);
       Stringa.Chara (true, false, true, true, false, true, true, false);
       Stringa.Chara (true, true, true, true, true, false, true, false);
       Stringa.Chara (false, false, true, false, true, true, true, false);
       Stringa.Chara (true, false, true, false, true, true, true, false);
       Stringa.Chara (false, false, false, false, true, true, true, false);
       Stringa.Chara (false, false, true, true, false, true, true, false);
       Stringa.Chara (true, false, true, false, false, true, true, false);
       Stringa.Chara (true, false, false, true, false, false, true, false);
       Stringa.Chara (false, false, false, false, false, true, false, false);
       Stringa.Chara (true, false, false, true, false, true, true, false);
       Stringa.Chara (false, false, true, false, true, true, false, false);
       Stringa.Chara (true, false, true, true, true, true, false, false)] @
      Show_Instances.shows_prec_nat Arith.Zero_nat i4 [] @
        Show_Instances.shows_prec_nat Arith.Zero_nat (Lista.size_list xalist)
          [])))
(fun () ->
  Predicate.bind (as_unpack_i_i_i_i_o_o i4 xa xas sa)
    (fun (saa, i5) -> Predicate.single (saa, i5)))))))))
            | (_, (_, (_, (_, (SailAST.Typ_app (_, _), _) :: _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (_, (SailAST.Typ_exist (_, _, _), _) :: _)))) ->
              Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
          (fun a ->
            (match a with (_, (_, (_, (_, [])))) -> Predicate.bot_pred
              | (i1, (env, (xmap, (pm, (b, xa) :: bss)))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      ([Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false);
                         Stringa.Chara
                           (false, false, false, false, false, true, false,
                             false);
                         Stringa.Chara
                           (false, true, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, true, true, true, false,
                             false)] @
                        ShowAST.shows_prec_typ Arith.Zero_nat b [])))
                  (fun () ->
                    Predicate.bind (Predicate.if_pred (is_literal_base b))
                      (fun () ->
                        Predicate.bind
                          (Predicate.if_pred
                            (trace
                              ([Stringa.Chara
                                  (true, true, false, false, false, true, true,
                                    false);
                                 Stringa.Chara
                                   (true, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, false, false, true, true,
                                     true, false);
                                 Stringa.Chara
                                   (true, false, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, false,
                                     true, false);
                                 Stringa.Chara
                                   (false, false, false, false, false, true,
                                     false, false);
                                 Stringa.Chara
                                   (true, false, false, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, false, true, true,
                                     false, false);
                                 Stringa.Chara
                                   (true, false, true, true, true, true, false,
                                     false)] @
                                Utils.string_of_nat i1)))
                          (fun () ->
                            Predicate.bind
                              (expand_lit_i_i_i_i_i_o_o_o i1 env xmap pm xa)
                              (fun (pmlits, (_, i3)) ->
                                Predicate.bind
                                  (Predicate.if_pred
                                    (trace
                                      ([Stringa.Chara
  (true, true, false, false, false, true, true, false);
 Stringa.Chara (true, true, true, true, false, true, true, false);
 Stringa.Chara (false, true, true, true, false, true, true, false);
 Stringa.Chara (false, true, true, false, true, true, true, false);
 Stringa.Chara (true, true, true, true, true, false, true, false);
 Stringa.Chara (false, false, false, false, true, true, true, false);
 Stringa.Chara (true, false, true, true, false, true, true, false);
 Stringa.Chara (true, true, true, true, true, false, true, false);
 Stringa.Chara (false, false, true, true, false, true, true, false);
 Stringa.Chara (true, false, false, true, false, true, true, false);
 Stringa.Chara (false, false, true, false, true, true, true, false);
 Stringa.Chara (true, false, false, true, false, false, true, false);
 Stringa.Chara (false, false, false, false, false, true, false, false);
 Stringa.Chara (true, false, false, true, false, true, true, false);
 Stringa.Chara (true, true, false, false, true, true, false, false);
 Stringa.Chara (true, false, true, true, true, true, false, false)] @
Utils.string_of_nat i3)))
                                  (fun () ->
                                    Predicate.bind
                                      (conv_pattern_matrix_list_i_i_i_i_o_o i3
env xmap
(Lista.map (fun pma -> (pma, bss)) (Lista.map Product_Type.fst pmlits)))
                                      (fun (salist, i4) ->
Predicate.bind
  (Predicate.if_pred
    (trace
      ([Stringa.Chara (true, true, false, false, false, true, true, false);
         Stringa.Chara (true, true, true, true, false, true, true, false);
         Stringa.Chara (false, true, true, true, false, true, true, false);
         Stringa.Chara (false, true, true, false, true, true, true, false);
         Stringa.Chara (true, true, true, true, true, false, true, false);
         Stringa.Chara (false, false, false, false, true, true, true, false);
         Stringa.Chara (true, false, true, true, false, true, true, false);
         Stringa.Chara (true, true, true, true, true, false, true, false);
         Stringa.Chara (false, false, true, true, false, true, true, false);
         Stringa.Chara (true, false, false, true, false, true, true, false);
         Stringa.Chara (false, false, true, false, true, true, true, false);
         Stringa.Chara (true, false, false, true, false, false, true, false);
         Stringa.Chara (false, false, false, false, false, true, false, false);
         Stringa.Chara (true, false, false, true, false, true, true, false);
         Stringa.Chara (false, false, true, false, true, true, false, false);
         Stringa.Chara (true, false, true, true, true, true, false, false)] @
        Utils.string_of_nat i4)))
  (fun () -> Predicate.single (mk_switch xa pmlits salist, i4)))))))))))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
            (fun a ->
              (match a with (_, (_, (_, (_, [])))) -> Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_internal_unknown, _) :: _)))) ->
                  Predicate.bot_pred
                | (i1, (env, (xmap, (pm, (SailAST.Typ_id tyid, xa) :: bss)))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind
                        (Predicate.if_pred
                          (not (is_literal_base (SailAST.Typ_id tyid))))
                        (fun () ->
                          Predicate.bind
                            (expand_ctor_i_i_i_i_i_o_o_o i1 env pm tyid xa)
                            (fun (pmctor, (_, i2)) ->
                              Predicate.bind
                                (Predicate.if_pred
                                  (trace
                                    ([Stringa.Chara
(true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (false, false, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, false, true, false, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, false, true, false, false);
                                       Stringa.Chara
 (true, false, false, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, false, false, true, true, false, false)] @
                                      Show_Instances.shows_prec_nat
Arith.Zero_nat i2 [])))
                                (fun () ->
                                  Predicate.bind
                                    (eq_o_i (mk_pm_list env tyid pmctor bss))
                                    (fun xf ->
                                      Predicate.bind
(conv_pattern_matrix_list_i_i_i_i_o_o i2 env xmap xf)
(fun (salist, i3) ->
  Predicate.bind
    (Predicate.if_pred
      (trace
        ([Stringa.Chara (true, true, false, false, false, true, true, false);
           Stringa.Chara (true, true, true, true, false, true, true, false);
           Stringa.Chara (false, true, true, true, false, true, true, false);
           Stringa.Chara (false, true, true, false, true, true, true, false);
           Stringa.Chara (true, true, true, true, true, false, true, false);
           Stringa.Chara (false, false, false, false, true, true, true, false);
           Stringa.Chara (true, false, true, true, false, true, true, false);
           Stringa.Chara (true, true, true, true, true, false, true, false);
           Stringa.Chara (true, true, false, false, false, true, true, false);
           Stringa.Chara (false, false, true, false, true, true, true, false);
           Stringa.Chara (true, true, true, true, false, true, true, false);
           Stringa.Chara (false, true, false, false, true, true, true, false);
           Stringa.Chara (true, false, false, true, false, false, true, false);
           Stringa.Chara
             (false, false, false, false, false, true, false, false);
           Stringa.Chara (true, false, false, true, false, true, true, false);
           Stringa.Chara (true, true, false, false, true, true, false, false)] @
          Show_Instances.shows_prec_nat Arith.Zero_nat i3 [])))
    (fun () -> Predicate.single (mk_match xa pmctor salist, i3))))))))
                | (_, (_, (_, (_, (SailAST.Typ_var _, _) :: _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_fn (_, _, _), _) :: _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_bidir (_, _, _), _) :: _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_tup _, _) :: _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_app (_, _), _) :: _)))) ->
                  Predicate.bot_pred
                | (_, (_, (_, (_, (SailAST.Typ_exist (_, _, _), _) :: _)))) ->
                  Predicate.bot_pred)))
          (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
                | (i1, (_, (_, (([], sa) :: _, [])))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, true, true, true, false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () -> Predicate.single (sa, i1))
                | (_, (_, (_, (([], _) :: _, _ :: _)))) -> Predicate.bot_pred
                | (_, (_, (_, ((_ :: _, _) :: _, _)))) ->
                  Predicate.bot_pred)))))
and conv_pattern_matrix_list_i_i_i_i_o_o
  x xb xc xd =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a
            with (i, (_, (_, []))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () -> Predicate.single ([], i))
            | (_, (_, (_, _ :: _))) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a with (_, (_, (_, []))) -> Predicate.bot_pred
            | (i1, (env, (xmap, (pm, bss) :: pmlist))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () ->
                  Predicate.bind
                    (conv_pattern_matrix_i_i_i_i_i_o_o i1 env xmap pm bss)
                    (fun (sa, i2) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Utils.string_of_nat i2)))
                        (fun () ->
                          Predicate.bind
                            (conv_pattern_matrix_list_i_i_i_i_o_o i2 env xmap
                              pmlist)
                            (fun (salist, i3) ->
                              Predicate.bind
                                (Predicate.if_pred
                                  (trace
                                    ([Stringa.Chara
(true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, false, true, false, false, true, false);
                                       Stringa.Chara
 (false, false, false, false, false, true, false, false);
                                       Stringa.Chara
 (true, false, false, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, false, true, true, false, false);
                                       Stringa.Chara
 (true, false, true, true, true, true, false, false)] @
                                      Utils.string_of_nat i3)))
                                (fun () ->
                                  Predicate.single (sa :: salist, i3)))))))));;

let rec v_conv_i_i_i_o_o_o
  x xb xc =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, xc)))
        (fun a ->
          (match a with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_lit (_, l))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, true, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () ->
                  Predicate.bind (lit_conv_i_o l)
                    (fun xa ->
                      Predicate.single ([], (Syntax.GNil, Syntax.V_lit xa))))
            | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_app_infix (_, _, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
              Predicate.bot_pred
            | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_vector_access (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
              Predicate.bot_pred
            | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
              Predicate.bot_pred
            | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
              Predicate.bot_pred
            | (_, (_, SailAST.E_vector_append (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_record_update (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
              Predicate.bot_pred
            | (_, (_, SailAST.E_internal_return (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_internal_value (_, _))) -> Predicate.bot_pred
            | (_, (_, SailAST.E_constraint (_, _))) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, xc)))
          (fun a ->
            (match a with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
              | (env, (xm, SailAST.E_id (_, idd))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      [Stringa.Chara
                         (false, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, true, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, false, true,
                            false)]))
                  (fun () ->
                    Predicate.bind (eq_o_i (Env.lookup SailAST.equal_id xm idd))
                      (fun aa ->
                        (match aa with None -> Predicate.bot_pred
                          | Some xa ->
                            Predicate.bind
                              (eq_o_i (Env.lookup_local_id_env env idd))
                              (fun ab ->
                                (match ab with None -> Predicate.bot_pred
                                  | Some t ->
                                    Predicate.bind (b_of_typ_i_o t)
                                      (fun xd ->
Predicate.bind
  (Predicate.if_pred
    (trace
      ([Stringa.Chara (false, true, true, false, true, true, true, false);
         Stringa.Chara (true, true, true, true, true, false, true, false);
         Stringa.Chara (true, true, false, false, false, true, true, false);
         Stringa.Chara (true, true, true, true, false, true, true, false);
         Stringa.Chara (false, true, true, true, false, true, true, false);
         Stringa.Chara (false, true, true, false, true, true, true, false);
         Stringa.Chara (true, true, true, true, true, false, true, false);
         Stringa.Chara (false, true, true, false, true, true, true, false);
         Stringa.Chara (true, false, false, false, false, true, true, false);
         Stringa.Chara (false, true, false, false, true, true, true, false);
         Stringa.Chara (true, false, false, true, false, false, true, false);
         Stringa.Chara (false, false, false, false, false, true, false, false);
         Stringa.Chara (true, false, true, false, false, true, true, false);
         Stringa.Chara (false, true, true, true, false, true, true, false);
         Stringa.Chara (false, false, true, false, false, true, true, false)] @
        cf xd)))
  (fun () ->
    Predicate.single
      ([], (Syntax.GCons ((xa, (xd, Syntax.C_true)), Syntax.GNil),
             Syntax.V_var xa)))))))))
              | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_app_infix (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_record_update (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_internal_return (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_internal_value (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_constraint (_, _))) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, xc)))
            (fun a ->
              (match a
                with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                | (env, (_, SailAST.E_id (_, SailAST.Id enum))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, false, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind
                        (eq_o_i (Env.lookup_enum_env env (SailAST.Id enum)))
                        (fun aa ->
                          (match aa with None -> Predicate.bot_pred
                            | Some SailAST.Typ_internal_unknown ->
                              Predicate.bot_pred
                            | Some (SailAST.Typ_id (SailAST.Id enum_id)) ->
                              Predicate.single
                                ([], (Syntax.GNil,
                                       Syntax.V_cons
 (Stringa.explode enum_id, Stringa.explode enum, Syntax.V_lit Syntax.L_unit)))
                            | Some (SailAST.Typ_id (SailAST.Operator _)) ->
                              Predicate.bot_pred
                            | Some (SailAST.Typ_var _) -> Predicate.bot_pred
                            | Some (SailAST.Typ_fn (_, _, _)) ->
                              Predicate.bot_pred
                            | Some (SailAST.Typ_bidir (_, _, _)) ->
                              Predicate.bot_pred
                            | Some (SailAST.Typ_tup _) -> Predicate.bot_pred
                            | Some (SailAST.Typ_app (_, _)) ->
                              Predicate.bot_pred
                            | Some (SailAST.Typ_exist (_, _, _)) ->
                              Predicate.bot_pred)))
                | (_, (_, SailAST.E_id (_, SailAST.Operator _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record_update (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_return (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_value (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_constraint (_, _))) -> Predicate.bot_pred)))
          (Predicate.bind (Predicate.single (x, (xb, xc)))
            (fun a ->
              (match a
                with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_tuple (_, []))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_tuple (_, [_]))) -> Predicate.bot_pred
                | (env, (m, SailAST.E_tuple (_, [vp1; vp2]))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, true, true,
                              false);
                          Stringa.Chara
                            (false, true, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind (v_conv_i_i_i_o_o_o env m vp1)
                        (fun (t1, (g1, v1)) ->
                          Predicate.bind (v_conv_i_i_i_o_o_o env m vp2)
                            (fun (t2, (g2, v2)) ->
                              Predicate.single
                                (t1 @ t2,
                                  (Syntax.append_g g1 g2,
                                    Syntax.V_pair (v1, v2))))))
                | (_, (_, SailAST.E_tuple (_, _ :: _ :: _ :: _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record_update (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_return (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_value (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_constraint (_, _))) ->
                  Predicate.bot_pred)))));;

let rec e_conv_i_i_i_i_o_o_o_o_o_o_o
  x xb xc xd =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun (n, (xm, (e, xa))) ->
          Predicate.bind
            (Predicate.if_pred
              (trace
                ([Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, true, false, false, false, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (false, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (false, true, true, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (false, true, true, false, true, true, true, false);
                   Stringa.Chara
                     (true, false, false, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, true, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, false, true, false, false, true, false);
                   Stringa.Chara
                     (false, false, false, false, false, true, false, false);
                   Stringa.Chara
                     (false, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, true, true, true, true, false, false)] @
                  Show_Instances.shows_prec_nat Arith.Zero_nat n [])))
            (fun () ->
              Predicate.bind (eq_o_i (Env.get_env_exp e))
                (fun a ->
                  (match a with None -> Predicate.bot_pred
                    | Some ea ->
                      Predicate.bind (v_conv_i_i_i_o_o_o ea xm e)
                        (fun (t, (g, va)) ->
                          Predicate.bind
                            (Predicate.if_pred
                              (trace
                                ([Stringa.Chara
                                    (true, false, true, false, false, true,
                                      true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, false, true, true,
                                       false);
                                   Stringa.Chara
                                     (false, true, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, true, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (false, true, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, false,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, false, false, true,
                                       false, false);
                                   Stringa.Chara
                                     (false, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, true, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, true, true, true,
                                       false, false)] @
                                  Show_Instances.shows_prec_nat Arith.Zero_nat
                                    (Lista.size_list t) [])))
                            (fun () ->
                              Predicate.single
                                (t, ([], (FSet.bot_fset,
   (g, (Syntax.DNil, (L_let (xa, Syntax.AE_val va, L_hole), n)))))))))))))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
          (fun a ->
            (match a
              with (_, (_, (SailAST.E_block (_, _), _))) -> Predicate.bot_pred
              | (n, (_, (SailAST.E_id (tan, reg), xa))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      ([Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false);
                         Stringa.Chara
                           (false, false, false, false, false, true, false,
                             false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, true, true, true, true, false,
                             false)] @
                        Show_Instances.shows_prec_nat Arith.Zero_nat n [])))
                  (fun () ->
                    Predicate.bind (eq_o_i (Env.get_env tan))
                      (fun aa ->
                        (match aa with None -> Predicate.bot_pred
                          | Some env ->
                            Predicate.bind
                              (eq_o_i (Env.lookup_register_index_env env reg))
                              (fun ab ->
                                (match ab with None -> Predicate.bot_pred
                                  | Some regi ->
                                    Predicate.bind
                                      (Predicate.if_pred
(trace
  ([Stringa.Chara (true, false, true, false, false, true, true, false);
     Stringa.Chara (true, true, true, true, true, false, true, false);
     Stringa.Chara (true, true, false, false, false, true, true, false);
     Stringa.Chara (true, true, true, true, false, true, true, false);
     Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (false, true, true, false, true, true, true, false);
     Stringa.Chara (true, true, true, true, true, false, true, false);
     Stringa.Chara (false, true, false, false, true, true, true, false);
     Stringa.Chara (true, false, true, false, false, true, true, false);
     Stringa.Chara (true, true, true, false, false, true, true, false);
     Stringa.Chara (true, false, false, true, false, false, true, false);
     Stringa.Chara (false, false, false, false, false, true, false, false);
     Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (true, false, true, true, true, true, false, false)] @
    Show_Instances.shows_prec_nat Arith.Zero_nat regi [])))
                                      (fun () ->
Predicate.bind (eq_o_i (Env.lookup_register_env env reg))
  (fun ac ->
    (match ac with None -> Predicate.bot_pred
      | Some typ ->
        Predicate.bind (t_conv_i_i_o [] typ)
          (fun xe ->
            Predicate.single
              ([], ([], (FSet.bot_fset,
                          (Syntax.GNil,
                            (Syntax.DCons ((mk_u regi, xe), Syntax.DNil),
                              (L_let (xa, Syntax.AE_mvar (mk_u regi), L_hole),
                                n)))))))))))))))
              | (_, (_, (SailAST.E_lit (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_cast (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_app (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_app_infix (_, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_tuple (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_if (_, _, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_loop (_, _, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_for (_, _, _, _, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_vector (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_vector_access (_, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_vector_subrange (_, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_vector_update (_, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_vector_update_subrange (_, _, _, _, _), _)))
                -> Predicate.bot_pred
              | (_, (_, (SailAST.E_vector_append (_, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_list (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_cons (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_record (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_record_update (_, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_field (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_case (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_let (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_assign (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_sizeof (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_return (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_exit (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_ref (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_throw (_, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_try (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_assert (_, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_var (_, _, _, _), _))) -> Predicate.bot_pred
              | (_, (_, (SailAST.E_internal_plet (_, _, _, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_internal_return (_, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_internal_value (_, _), _))) ->
                Predicate.bot_pred
              | (_, (_, (SailAST.E_constraint (_, _), _))) ->
                Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
            (fun a ->
              (match a
                with (_, (_, (SailAST.E_block (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_id (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_lit (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_cast (_, _, _), _))) -> Predicate.bot_pred
                | (n1, (xm, (SailAST.E_app (_, SailAST.Id fid, es), xa))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, false, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind (eq_o_i (mk_fresh_x n1))
                        (fun (n2, xaa) ->
                          Predicate.bind
                            (e_conv_list_i_i_i_i_o_o_o_o_o_o_o n2 xm es xaa)
                            (fun (t, (p, (b, (g, (d, (l, n3)))))) ->
                              Predicate.single
                                (t, (p, (b,
  (g, (d, (L_compose
             (l, L_let (xa, Syntax.AE_app
                              (Stringa.explode fid, Syntax.V_var xaa),
                         L_hole)),
            n3)))))))))
                | (_, (_, (SailAST.E_app (_, SailAST.Operator _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_app_infix (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_tuple (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_if (_, _, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_loop (_, _, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_for (_, _, _, _, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_access (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_subrange (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_update (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_update_subrange (_, _, _, _, _),
                            _)))
                  -> Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_append (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_list (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_cons (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_record (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_record_update (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_field (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_case (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_let (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_assign (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_sizeof (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_return (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_exit (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_ref (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_throw (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_try (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_assert (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_var (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_plet (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_return (_, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_value (_, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_constraint (_, _), _))) ->
                  Predicate.bot_pred)))
          (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
            (fun a ->
              (match a
                with (_, (_, (SailAST.E_block (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_id (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_lit (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_cast (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_app (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_app_infix (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (n1, (xm, (SailAST.E_tuple (_, es), xa))) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (false, false, true, false, true, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, false, false, false, true, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, true, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind
                        (e_conv_list_i_i_i_i_o_o_o_o_o_o_o n1 xm es xa)
                        (fun (t, (p, (b, (g, (d, (l, n2)))))) ->
                          Predicate.single (t, (p, (b, (g, (d, (l, n2))))))))
                | (_, (_, (SailAST.E_if (_, _, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_loop (_, _, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_for (_, _, _, _, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_access (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_subrange (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_update (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_update_subrange (_, _, _, _, _),
                            _)))
                  -> Predicate.bot_pred
                | (_, (_, (SailAST.E_vector_append (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_list (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_cons (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_record (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_record_update (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_field (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_case (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_let (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_assign (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_sizeof (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_return (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_exit (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_ref (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_throw (_, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_try (_, _, _), _))) -> Predicate.bot_pred
                | (_, (_, (SailAST.E_assert (_, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_var (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_plet (_, _, _, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_return (_, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_internal_value (_, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, (SailAST.E_constraint (_, _), _))) ->
                  Predicate.bot_pred)))))
and e_conv_list_i_i_i_i_o_o_o_o_o_o_o
  x xb xc xd =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a with (_, (_, ([], _))) -> Predicate.bot_pred
            | (n1, (xm, ([e], xa))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    ([Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (false, false, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (false, false, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, false, true, false);
                       Stringa.Chara
                         (false, false, false, false, false, true, false,
                           false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, true, true, false, false);
                       Stringa.Chara
                         (true, false, true, true, true, true, false, false)] @
                      Show_Instances.shows_prec_nat Arith.Zero_nat n1 [])))
                (fun () ->
                  Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o n1 xm e xa)
                    (fun (t, (p, (b, (g, (d, (l, n2)))))) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Show_Instances.shows_prec_nat Arith.Zero_nat n2
                                [])))
                        (fun () ->
                          Predicate.single (t, (p, (b, (g, (d, (l, n2)))))))))
            | (_, (_, (_ :: _ :: _, _))) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, (xb, (xc, xd))))
        (fun a ->
          (match a with (_, (_, ([], _))) -> Predicate.bot_pred
            | (n1, (xm, (e :: es, xa))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    ([Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (false, false, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (false, false, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, false, true, false);
                       Stringa.Chara
                         (false, false, false, false, false, true, false,
                           false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, true, true, false, false);
                       Stringa.Chara
                         (true, false, true, true, true, true, false, false)] @
                      Show_Instances.shows_prec_nat Arith.Zero_nat n1 [])))
                (fun () ->
                  Predicate.bind (eq_o_i (mk_fresh_x n1))
                    (fun (n2, xaa) ->
                      Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o n2 xm e xaa)
                        (fun (_, (_, (_, (_, (_, (l1, n3)))))) ->
                          Predicate.bind
                            (Predicate.if_pred
                              (trace
                                ([Stringa.Chara
                                    (true, false, true, false, false, true,
                                      true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, false, true, true,
                                       false);
                                   Stringa.Chara
                                     (false, true, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, true, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (false, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, false, true, true,
                                       false);
                                   Stringa.Chara
                                     (false, true, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, false,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, false, false, true,
                                       false, false);
                                   Stringa.Chara
                                     (false, true, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, false, true, true,
                                       false, false);
                                   Stringa.Chara
                                     (true, false, true, true, true, true,
                                       false, false)] @
                                  Show_Instances.shows_prec_nat Arith.Zero_nat
                                    n3 [])))
                            (fun () ->
                              Predicate.bind (eq_o_i (mk_fresh_x n3))
                                (fun (n4, xab) ->
                                  Predicate.bind
                                    (e_conv_list_i_i_i_i_o_o_o_o_o_o_o n4 xm es
                                      xab)
                                    (fun (t, (p, (b, (g, (d, (l2, n5)))))) ->
                                      Predicate.bind
(Predicate.if_pred
  (trace
    ([Stringa.Chara (true, false, true, false, false, true, true, false);
       Stringa.Chara (true, true, true, true, true, false, true, false);
       Stringa.Chara (true, true, false, false, false, true, true, false);
       Stringa.Chara (true, true, true, true, false, true, true, false);
       Stringa.Chara (false, true, true, true, false, true, true, false);
       Stringa.Chara (false, true, true, false, true, true, true, false);
       Stringa.Chara (true, true, true, true, true, false, true, false);
       Stringa.Chara (false, false, true, true, false, true, true, false);
       Stringa.Chara (true, false, false, true, false, true, true, false);
       Stringa.Chara (true, true, false, false, true, true, true, false);
       Stringa.Chara (false, false, true, false, true, true, true, false);
       Stringa.Chara (true, true, true, true, true, false, true, false);
       Stringa.Chara (true, true, false, false, false, true, true, false);
       Stringa.Chara (true, true, true, true, false, true, true, false);
       Stringa.Chara (false, true, true, true, false, true, true, false);
       Stringa.Chara (true, true, false, false, true, true, true, false);
       Stringa.Chara (true, false, false, true, false, false, true, false);
       Stringa.Chara (false, false, false, false, false, true, false, false);
       Stringa.Chara (false, true, true, true, false, true, true, false);
       Stringa.Chara (true, false, true, false, true, true, false, false);
       Stringa.Chara (true, false, true, true, true, true, false, false)] @
      Show_Instances.shows_prec_nat Arith.Zero_nat n5 [])))
(fun () ->
  Predicate.single
    (t, (p, (b, (g, (d, (L_compose
                           (l1, L_compose
                                  (l2, L_let
 (xa, Syntax.AE_val (Syntax.V_pair (Syntax.V_var xaa, Syntax.V_var xab)),
   L_hole))),
                          n5))))))))))))))));;

let rec pexp_list_conv_i_i_i_i_i_o_o
  x xb xc xd xe =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
        (fun a ->
          (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
            | (i1, (_, (xm, ([SailAST.Pat_exp (_, patp, ep)], _)))) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    ([Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, false, true, true, false);
                       Stringa.Chara
                         (false, true, false, false, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (false, false, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, false, true, true, true, true, false);
                       Stringa.Chara
                         (false, false, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, true, false, true, false);
                       Stringa.Chara
                         (true, true, false, false, true, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, true, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, true, false, false, true, true, false);
                       Stringa.Chara
                         (false, false, true, false, true, true, true, false);
                       Stringa.Chara
                         (true, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (false, true, true, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, true, false, false, true, false);
                       Stringa.Chara
                         (false, false, false, false, false, true, false,
                           false);
                       Stringa.Chara
                         (true, false, false, true, false, true, true, false);
                       Stringa.Chara
                         (true, false, false, false, true, true, false, false);
                       Stringa.Chara
                         (true, false, true, true, true, true, false, false)] @
                      Show_Instances.shows_prec_nat Arith.Zero_nat i1 [])))
                (fun () ->
                  Predicate.bind (s_conv_i_i_i_o_o_o_o_o_o_o i1 xm ep)
                    (fun (_, (_, (_, (_, (_, (sa, i2)))))) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Show_Instances.shows_prec_nat Arith.Zero_nat i2
                                [])))
                        (fun () -> Predicate.single ([([patp], sa)], i2))))
            | (_, (_, (_, (SailAST.Pat_exp (_, _, _) :: _ :: _, _)))) ->
              Predicate.bot_pred
            | (_, (_, (_, (SailAST.Pat_when (_, _, _, _) :: _, _)))) ->
              Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, (xb, (xc, (xd, xe)))))
        (fun a ->
          (match a with (_, (_, (_, ([], _)))) -> Predicate.bot_pred
            | (_, (_, (_, ([SailAST.Pat_exp (_, _, _)], _)))) ->
              Predicate.bot_pred
            | (i1, (env, (xm, (SailAST.Pat_exp (_, patp, ep) :: pexp :: pexps,
                                xa))))
              -> Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, true, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (s_conv_i_i_i_o_o_o_o_o_o_o i1 xm ep)
                       (fun (_, (_, (_, (_, (_, (sa, i2)))))) ->
                         Predicate.bind
                           (pexp_list_conv_i_i_i_i_i_o_o i2 env xm
                             (pexp :: pexps) xa)
                           (fun (pm, i3) ->
                             Predicate.single (([patp], sa) :: pm, i3))))
            | (_, (_, (_, (SailAST.Pat_when (_, _, _, _) :: _, _)))) ->
              Predicate.bot_pred)))
and s_conv_i_i_i_o_o_o_o_o_o_o
  x xb xc =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xb, xc)))
        (fun (n1, (xm, e)) ->
          Predicate.bind
            (Predicate.if_pred
              (trace
                ([Stringa.Chara
                    (true, true, false, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, true, false, false, false, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (false, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (false, true, true, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, false, true, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, false, true, true, true, true, false);
                   Stringa.Chara
                     (false, false, false, false, true, true, true, false);
                   Stringa.Chara
                     (true, false, false, true, false, false, true, false);
                   Stringa.Chara
                     (false, false, false, false, false, true, false, false);
                   Stringa.Chara
                     (false, true, true, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, false, false, true, true, false, false);
                   Stringa.Chara
                     (true, false, true, true, true, true, false, false)] @
                  Show_Instances.shows_prec_nat Arith.Zero_nat n1 [])))
            (fun () ->
              Predicate.bind (eq_o_i (mk_fresh_x n1))
                (fun (n2, xa) ->
                  Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o n2 xm e xa)
                    (fun (t, (p, (b, (g, (d, (l, n3)))))) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, true, false, false, true, true, true,
                                  false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (false, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Show_Instances.shows_prec_nat Arith.Zero_nat n3
                                [])))
                        (fun () ->
                          Predicate.single
                            (t, (p, (b, (g,
  (d, (lctx_apply l (Syntax.AS_val (Syntax.V_var xa)), n3))))))))))))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xb, xc)))
          (fun a ->
            (match a
              with (_, (_, SailAST.E_block (_, []))) -> Predicate.bot_pred
              | (n1, (xm, SailAST.E_block (_, [e]))) ->
                Predicate.bind
                  (Predicate.if_pred
                    (trace
                      ([Stringa.Chara
                          (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, true, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false);
                         Stringa.Chara
                           (false, false, false, false, false, true, false,
                             false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, true, true, false,
                             false);
                         Stringa.Chara
                           (true, false, true, true, true, true, false,
                             false)] @
                        Show_Instances.shows_prec_nat Arith.Zero_nat n1 [])))
                  (fun () ->
                    Predicate.bind (s_conv_i_i_i_o_o_o_o_o_o_o n1 xm e)
                      (fun (t, (p, (b, (g, (d, (la, n2)))))) ->
                        Predicate.bind
                          (Predicate.if_pred
                            (trace
                              ([Stringa.Chara
                                  (true, true, false, false, true, true, true,
                                    false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, false, false, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, true, false, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, false, false, false, true,
                                     true, false);
                                 Stringa.Chara
                                   (false, false, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, false, false, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, true, false, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, false,
                                     true, false);
                                 Stringa.Chara
                                   (false, false, false, false, false, true,
                                     false, false);
                                 Stringa.Chara
                                   (false, true, true, true, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, true, false, false, true, true,
                                     false, false);
                                 Stringa.Chara
                                   (true, false, true, true, true, true, false,
                                     false)] @
                                Show_Instances.shows_prec_nat Arith.Zero_nat n2
                                  [])))
                          (fun () ->
                            Predicate.single
                              (t, (p, (b, (g, (d, (la, n2)))))))))
              | (_, (_, SailAST.E_block (_, _ :: _ :: _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_app_infix (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_record_update (_, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                Predicate.bot_pred
              | (_, (_, SailAST.E_internal_return (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_internal_value (_, _))) -> Predicate.bot_pred
              | (_, (_, SailAST.E_constraint (_, _))) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xb, xc)))
            (fun a ->
              (match a
                with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_loop (_, _, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_record_update (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
                | (n1, (xm, SailAST.E_assign
                              (tan, SailAST.LEXP_id (_, regid), e)))
                  -> Predicate.bind (eq_o_i (mk_fresh_x n1))
                       (fun (n2, xa) ->
                         Predicate.bind (eq_o_i (Env.get_env tan))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some env ->
                                 Predicate.bind
                                   (eq_o_i
                                     (Env.lookup_register_index_env env regid))
                                   (fun ab ->
                                     (match ab with None -> Predicate.bot_pred
                                       | Some regi ->
 Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o n2 xm e xa)
   (fun (t, (p, (b, (g, (d, (l, n3)))))) ->
     Predicate.single
       (t, (p, (b, (g, (d, (lctx_apply l
                              (Syntax.AS_assign (mk_u regi, Syntax.V_var xa)),
                             n3))))))))))))
                | (_, (_, SailAST.E_assign (_, SailAST.LEXP_deref (_, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign
                            (_, SailAST.LEXP_memory (_, _, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign (_, SailAST.LEXP_cast (_, _, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign (_, SailAST.LEXP_tup (_, _), _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_assign
                            (_, SailAST.LEXP_vector_concat (_, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign
                            (_, SailAST.LEXP_vector (_, _, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign
                            (_, SailAST.LEXP_vector_range (_, _, _, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_assign
                            (_, SailAST.LEXP_field (_, _, _), _)))
                  -> Predicate.bot_pred
                | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_return (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_internal_value (_, _))) ->
                  Predicate.bot_pred
                | (_, (_, SailAST.E_constraint (_, _))) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xb, xc)))
              (fun a ->
                (match a
                  with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
                  | (n1, (xm, SailAST.E_if (_, e1, e2, e3))) ->
                    Predicate.bind (eq_o_i (mk_fresh_x n1))
                      (fun (n2, xa) ->
                        Predicate.bind
                          (e_conv_i_i_i_i_o_o_o_o_o_o_o n2 xm e1 xa)
                          (fun (_, (_, (_, (_, (_, (l, n3)))))) ->
                            Predicate.bind (s_conv_i_i_i_o_o_o_o_o_o_o n3 xm e2)
                              (fun (_, (_, (_, (_, (_, (sa2, n4)))))) ->
                                Predicate.bind
                                  (s_conv_i_i_i_o_o_o_o_o_o_o n4 xm e3)
                                  (fun (t3, (p3, (b3, (g3, (d3, (sa3, _)))))) ->
                                    Predicate.single
                                      (t3,
(p3, (b3, (g3, (d3, (lctx_apply l (Syntax.AS_if (Syntax.V_var xa, sa2, sa3)),
                      n4))))))))))
                  | (_, (_, SailAST.E_loop (_, _, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _)))
                    -> Predicate.bot_pred
                  | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_record_update (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                  | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_internal_return (_, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_internal_value (_, _))) ->
                    Predicate.bot_pred
                  | (_, (_, SailAST.E_constraint (_, _))) ->
                    Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, (xb, xc)))
                (fun a ->
                  (match a
                    with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_loop (_, _, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _)))
                      -> Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_record_update (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_case (_, _, _))) -> Predicate.bot_pred
                    | (i1, (xm, SailAST.E_let
                                  (tan, SailAST.LB_val (_, pat, e1), e2)))
                      -> Predicate.bind
                           (Predicate.if_pred
                             (trace
                               [Stringa.Chara
                                  (false, false, true, true, false, true, true,
                                    false);
                                 Stringa.Chara
                                   (true, false, true, false, false, true, true,
                                     false);
                                 Stringa.Chara
                                   (false, false, true, false, true, true, true,
                                     false);
                                 Stringa.Chara
                                   (true, false, false, true, false, false,
                                     true, false)]))
                           (fun () ->
                             Predicate.bind (eq_o_i (mk_fresh_x i1))
                               (fun (i2, xa) ->
                                 Predicate.bind (eq_o_i (Env.type_of_exp e1))
                                   (fun aa ->
                                     (match aa with None -> Predicate.bot_pred
                                       | Some t ->
 Predicate.bind
   (Predicate.if_pred
     (trace
       ([Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, false, true, true, true, true, false, false)] @
         ShowAST.shows_prec_typ Arith.Zero_nat t [])))
   (fun () ->
     Predicate.bind (eq_o_i (Env.get_env tan))
       (fun ab ->
         (match ab with None -> Predicate.bot_pred
           | Some env ->
             Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o i2 xm e1 xa)
               (fun (t1, (p1, (b1, (g1, (d1, (l, i3)))))) ->
                 Predicate.bind
                   (pexp_list_conv_i_i_i_i_i_o_o i3 env xm
                     [SailAST.Pat_exp (None, pat, e2)] xa)
                   (fun (pm, i4) ->
                     Predicate.bind
                       (Predicate.if_pred
                         (trace
                           ([Stringa.Chara
                               (false, false, true, false, false, true, true,
                                 false);
                              Stringa.Chara
                                (true, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, false, true, false,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, true, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, false, true, false,
                                  false);
                              Stringa.Chara
                                (false, false, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, false, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, false, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, false, false, false, true, false,
                                  false);
                              Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, false, true, true, true,
                                  false)] @
                             mk_str pm @ Utils.string_of_nat i4)))
                       (fun () ->
                         Predicate.bind
                           (conv_pattern_matrix_i_i_i_i_i_o_o i4 env xm pm
                             [(t, xa)])
                           (fun (sa, i5) ->
                             Predicate.bind
                               (Predicate.if_pred
                                 (trace
                                   ([Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                      Stringa.Chara
(false, false, true, true, false, true, true, false);
                                      Stringa.Chara
(true, false, false, false, false, true, true, false);
                                      Stringa.Chara
(false, true, false, false, false, true, true, false);
                                      Stringa.Chara
(false, false, false, false, false, true, false, false);
                                      Stringa.Chara
(true, false, false, true, false, true, true, false);
                                      Stringa.Chara
(true, false, true, false, true, true, false, false);
                                      Stringa.Chara
(true, false, true, true, true, true, false, false)] @
                                     Utils.string_of_nat i5)))
                               (fun () ->
                                 Predicate.single
                                   (t1, (p1,
  (b1, (g1, (d1, (lctx_apply l sa, i5))))))))))))))))))
                    | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_return (_, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_value (_, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_constraint (_, _))) ->
                      Predicate.bot_pred)))
              (Predicate.bind (Predicate.single (x, (xb, xc)))
                (fun a ->
                  (match a
                    with (_, (_, SailAST.E_block (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_id (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_lit (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_cast (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_app (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_app_infix (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_tuple (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_if (_, _, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_loop (_, _, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_for (_, _, _, _, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_access (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_subrange (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_update (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_update_subrange (_, _, _, _, _)))
                      -> Predicate.bot_pred
                    | (_, (_, SailAST.E_vector_append (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_list (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_cons (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_record (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_record_update (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_field (_, _, _))) -> Predicate.bot_pred
                    | (i1, (xm, SailAST.E_case (tan, ep, pexps))) ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            ([Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, false, true, true, false,
                                   false);
                               Stringa.Chara
                                 (true, false, true, true, true, true, false,
                                   false)] @
                              Show_Instances.shows_prec_nat Arith.Zero_nat i1
                                [])))
                        (fun () ->
                          Predicate.bind (eq_o_i (Env.get_env tan))
                            (fun aa ->
                              (match aa with None -> Predicate.bot_pred
                                | Some env ->
                                  Predicate.bind (eq_o_i (mk_fresh_x i1))
                                    (fun (i2, xa) ->
                                      Predicate.bind
(eq_o_i (Env.type_of_exp ep))
(fun ab ->
  (match ab with None -> Predicate.bot_pred
    | Some t ->
      Predicate.bind (e_conv_i_i_i_i_o_o_o_o_o_o_o i2 xm ep xa)
        (fun (ta, (p, (b, (g, (d, (l, i3)))))) ->
          Predicate.bind
            (Predicate.if_pred
              (trace
                ([Stringa.Chara
                    (true, false, true, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, false, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, true, false, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, false, true, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, true, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, false, false, false, true, true, false);
                   Stringa.Chara
                     (false, true, false, false, false, true, true, false);
                   Stringa.Chara
                     (true, true, true, true, true, false, true, false);
                   Stringa.Chara
                     (true, false, true, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, false, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, true, false, true, true, true, false);
                   Stringa.Chara
                     (true, true, false, false, false, true, true, false);
                   Stringa.Chara
                     (false, false, false, true, false, true, true, false);
                   Stringa.Chara
                     (true, false, false, true, false, false, true, false);
                   Stringa.Chara
                     (false, false, false, false, false, true, false, false);
                   Stringa.Chara
                     (true, false, false, true, false, true, true, false);
                   Stringa.Chara
                     (true, true, false, false, true, true, false, false);
                   Stringa.Chara
                     (true, false, true, true, true, true, false, false)] @
                  Show_Instances.shows_prec_nat Arith.Zero_nat i3 [])))
            (fun () ->
              Predicate.bind (pexp_list_conv_i_i_i_i_i_o_o i3 env xm pexps xa)
                (fun (pm, i4) ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        ([Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (true, true, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (true, false, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, false, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, false, true, false,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, true, true, false,
                               false);
                           Stringa.Chara
                             (true, false, true, true, true, true, false,
                               false)] @
                          Show_Instances.shows_prec_nat Arith.Zero_nat i4 [])))
                    (fun () ->
                      Predicate.bind
                        (conv_pattern_matrix_i_i_i_i_i_o_o i4 env xm pm
                          [(t, xa)])
                        (fun (sa, i5) ->
                          Predicate.bind
                            (Predicate.if_pred
                              (trace
                                ([Stringa.Chara
                                    (true, false, true, false, false, true,
                                      true, false);
                                   Stringa.Chara
                                     (false, false, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, true, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, false, true, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (true, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, false,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, false, false, true,
                                       false, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, false, true, true,
                                       false, false);
                                   Stringa.Chara
                                     (true, false, true, true, true, true,
                                       false, false)] @
                                  Show_Instances.shows_prec_nat Arith.Zero_nat
                                    i5 [])))
                            (fun () ->
                              Predicate.single
                                (ta, (p, (b,
   (g, (d, (lctx_apply l sa, i5))))))))))))))))))
                    | (_, (_, SailAST.E_let (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_assign (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_sizeof (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_return (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_exit (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_ref (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_throw (_, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_try (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_assert (_, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_var (_, _, _, _))) -> Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_plet (_, _, _, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_return (_, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_internal_value (_, _))) ->
                      Predicate.bot_pred
                    | (_, (_, SailAST.E_constraint (_, _))) ->
                      Predicate.bot_pred)))))));;

let rec funcl_conv_i_i_i_o
  x xb xc =
    Predicate.bind (Predicate.single (x, (xb, xc)))
      (fun (env, (_, funcls)) ->
        Predicate.bind (eq_o_i (mk_fresh_x Arith.Zero_nat))
          (fun (i1, xa) ->
            Predicate.bind
              (eq_o_i
                (Lista.map (fun (SailAST.PEXP_funcl pexp) -> pexp) funcls))
              (fun xd ->
                Predicate.bind (eq_o_i (mk_id_map xd))
                  (fun xba ->
                    Predicate.bind (eq_o_i (Env.type_of_pexp (Lista.hd xd)))
                      (fun a ->
                        (match a with None -> Predicate.bot_pred
                          | Some t ->
                            Predicate.bind
                              (Predicate.if_pred
                                (trace
                                  ([Stringa.Chara
                                      (false, true, true, false, false, true,
true, false);
                                     Stringa.Chara
                                       (true, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, false, true, true,
 true, false)] @
                                    ShowAST.shows_prec_typ Arith.Zero_nat t
                                      [])))
                              (fun () ->
                                Predicate.bind
                                  (pexp_list_conv_i_i_i_i_i_o_o i1 env xba xd
                                    xa)
                                  (fun (pm, i4) ->
                                    Predicate.bind
                                      (Predicate.if_pred
(trace
  ([Stringa.Chara (false, true, true, false, false, true, true, false);
     Stringa.Chara (true, false, true, false, true, true, true, false);
     Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (true, true, false, false, false, true, true, false);
     Stringa.Chara (false, false, true, true, false, true, true, false);
     Stringa.Chara (true, true, true, true, true, false, true, false);
     Stringa.Chara (true, true, false, false, false, true, true, false);
     Stringa.Chara (true, true, true, true, false, true, true, false);
     Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (false, true, true, false, true, true, true, false);
     Stringa.Chara (false, false, false, false, false, true, false, false);
     Stringa.Chara (true, false, false, true, false, true, true, false);
     Stringa.Chara (false, false, true, false, true, true, false, false);
     Stringa.Chara (true, false, true, true, true, true, false, false)] @
    Utils.string_of_nat i4)))
                                      (fun () ->
Predicate.bind (conv_pattern_matrix_i_i_i_i_i_o_o i4 env xba pm [(t, xa)])
  (fun (sa, i5) ->
    Predicate.bind
      (Predicate.if_pred
        (trace
          ([Stringa.Chara (false, true, true, false, false, true, true, false);
             Stringa.Chara (true, false, true, false, true, true, true, false);
             Stringa.Chara (false, true, true, true, false, true, true, false);
             Stringa.Chara (true, true, false, false, false, true, true, false);
             Stringa.Chara (false, false, true, true, false, true, true, false);
             Stringa.Chara (true, true, true, true, true, false, true, false);
             Stringa.Chara (true, true, false, false, false, true, true, false);
             Stringa.Chara (true, true, true, true, false, true, true, false);
             Stringa.Chara (false, true, true, true, false, true, true, false);
             Stringa.Chara (false, true, true, false, true, true, true, false);
             Stringa.Chara
               (false, false, false, false, false, true, false, false);
             Stringa.Chara (true, false, false, true, false, true, true, false);
             Stringa.Chara (true, false, true, false, true, true, false, false);
             Stringa.Chara
               (true, false, true, true, true, true, false, false)] @
            Utils.string_of_nat i5)))
      (fun () ->
        Predicate.single
          (Syntax.AS_let
            (xa, Syntax.AE_snd (Syntax.V_var (mk_x Arith.one_nat)),
              sa)))))))))))));;

let rec lookup_fun_typ env f = Env.get_val_spec_env env (SailAST.Id f);;

let rec def_conv_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
            | (_, SailAST.DEF_fundef (SailAST.FD_function (_, _, _, _, []))) ->
              Predicate.bot_pred
            | (_, SailAST.DEF_fundef
                    (SailAST.FD_function
                      (_, _, _, _,
                        SailAST.FCL_Funcl (tan, SailAST.Id f, pexp_funcl) ::
                          fcls)))
              -> Predicate.bind (eq_o_i (extract_tan tan fcls))
                   (fun xb ->
                     Predicate.bind (eq_o_i (Env.get_env xb))
                       (fun aa ->
                         (match aa with None -> Predicate.bot_pred
                           | Some env ->
                             Predicate.bind
                               (Predicate.if_pred
                                 (trace
                                   ([Stringa.Chara
                                       (false, false, true, false, false, true,
 true, false);
                                      Stringa.Chara
(true, false, true, false, false, true, true, false);
                                      Stringa.Chara
(false, true, true, false, false, true, true, false);
                                      Stringa.Chara
(true, true, true, true, true, false, true, false);
                                      Stringa.Chara
(true, true, false, false, false, true, true, false);
                                      Stringa.Chara
(true, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, true, true, false, true, true, true, false);
                                      Stringa.Chara
(true, true, true, true, true, false, true, false);
                                      Stringa.Chara
(true, false, false, false, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(true, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, false, true, false, true, true, true, false);
                                      Stringa.Chara
(true, true, true, true, true, false, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(true, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(true, false, true, false, false, true, true, false);
                                      Stringa.Chara
(false, false, false, false, false, true, false, false);
                                      Stringa.Chara
(true, false, true, false, false, true, true, false);
                                      Stringa.Chara
(false, true, true, true, false, true, true, false);
                                      Stringa.Chara
(false, true, true, false, true, true, true, false);
                                      Stringa.Chara
(true, false, true, true, true, true, false, false)] @
                                     ShowAST.show_env env)))
                               (fun () ->
                                 Predicate.bind (eq_o_i (lookup_fun_typ env f))
                                   (fun ab ->
                                     (match ab with None -> Predicate.bot_pred
                                       | Some (tyq, fntyp) ->
 Predicate.bind
   (Predicate.if_pred
     (trace
       ([Stringa.Chara (false, false, true, false, false, true, true, false);
          Stringa.Chara (true, false, true, false, false, true, true, false);
          Stringa.Chara (false, true, true, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (true, true, false, false, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, false, true, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (true, false, false, false, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, true, true, true, true, false, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, true, true, true, false, true, true, false);
          Stringa.Chara (false, true, true, true, false, true, true, false);
          Stringa.Chara (true, false, true, false, false, true, true, false);
          Stringa.Chara (false, false, false, false, false, true, false, false);
          Stringa.Chara (false, false, true, false, true, true, true, false);
          Stringa.Chara (true, false, false, true, true, true, true, false);
          Stringa.Chara (false, false, false, false, true, true, true, false);
          Stringa.Chara (true, false, true, true, true, true, false, false)] @
         ShowAST.shows_prec_typ Arith.Zero_nat fntyp [])))
   (fun () ->
     Predicate.bind (eq_o_i (mk_tq_map tyq))
       (fun xc ->
         Predicate.bind (eq_o_i (extract_pexp fcls))
           (fun xaa ->
             Predicate.bind (funcl_conv_i_i_i_o env xc (pexp_funcl :: xaa))
               (fun xd ->
                 Predicate.bind (def_funtyp_i_i_o_o_o tyq fntyp)
                   (fun (ba, (ca, ta)) ->
                     Predicate.single
                       (Some (MS_fun_def
                               (Syntax.AF_fundef
                                 (Stringa.explode f,
                                   Syntax.AF_fun_typ_none
                                     (Syntax.AF_fun_typ
                                       (mk_x Arith.one_nat, ba, ca, ta,
 xd)))))))))))))))))
            | (_, SailAST.DEF_fundef
                    (SailAST.FD_function
                      (_, _, _, _,
                        SailAST.FCL_Funcl (_, SailAST.Operator _, _) :: _)))
              -> Predicate.bot_pred
            | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
            | (_, SailAST.DEF_val _) -> Predicate.bot_pred
            | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_default _) -> Predicate.bot_pred
            | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
            | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a
              with (_, SailAST.DEF_type
                         (SailAST.TD_aux (SailAST.TD_abbrev (_, _, _))))
                -> Predicate.bot_pred
              | (_, SailAST.DEF_type
                      (SailAST.TD_aux (SailAST.TD_record (_, _, _, _))))
                -> Predicate.bot_pred
              | (env, SailAST.DEF_type
                        (SailAST.TD_aux
                          (SailAST.TD_variant
                            (SailAST.Id tyid, _, tu_list, _))))
                -> Predicate.bind (variant_conv_i_i_o env tu_list)
                     (fun xb ->
                       Predicate.single
                         (Some (MS_type_def
                                 (Syntax.AF_typedef
                                   (Stringa.explode tyid, xb)))))
              | (_, SailAST.DEF_type
                      (SailAST.TD_aux
                        (SailAST.TD_variant (SailAST.Operator _, _, _, _))))
                -> Predicate.bot_pred
              | (_, SailAST.DEF_type
                      (SailAST.TD_aux (SailAST.TD_enum (_, _, _))))
                -> Predicate.bot_pred
              | (_, SailAST.DEF_type
                      (SailAST.TD_aux (SailAST.TD_bitfield (_, _, _))))
                -> Predicate.bot_pred
              | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
              | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
              | (_, SailAST.DEF_val _) -> Predicate.bot_pred
              | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_default _) -> Predicate.bot_pred
              | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
              | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a
                with (_, SailAST.DEF_type
                           (SailAST.TD_aux (SailAST.TD_abbrev (_, _, _))))
                  -> Predicate.bot_pred
                | (_, SailAST.DEF_type
                        (SailAST.TD_aux (SailAST.TD_record (_, _, _, _))))
                  -> Predicate.bot_pred
                | (_, SailAST.DEF_type
                        (SailAST.TD_aux (SailAST.TD_variant (_, _, _, _))))
                  -> Predicate.bot_pred
                | (env, SailAST.DEF_type
                          (SailAST.TD_aux
                            (SailAST.TD_enum (SailAST.Id tyid, id_list, _))))
                  -> Predicate.bind
                       (eq_o_i
                         (Lista.map
                           (fun aa -> SailAST.Tu_ty_id (AstUtils.unit_typ, aa))
                           id_list))
                       (fun xb ->
                         Predicate.bind (variant_conv_i_i_o env xb)
                           (fun xc ->
                             Predicate.single
                               (Some (MS_type_def
                                       (Syntax.AF_typedef
 (Stringa.explode tyid, xc))))))
                | (_, SailAST.DEF_type
                        (SailAST.TD_aux
                          (SailAST.TD_enum (SailAST.Operator _, _, _))))
                  -> Predicate.bot_pred
                | (_, SailAST.DEF_type
                        (SailAST.TD_aux (SailAST.TD_bitfield (_, _, _))))
                  -> Predicate.bot_pred
                | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_spec
                          (SailAST.VS_aux
                            (SailAST.TypSchm_ts (tyq, typ),
                              (SailAST.Id f, (_, _)))))
                    -> Predicate.bind (def_funtyp_i_i_o_o_o tyq typ)
                         (fun (ba, (ca, ta)) ->
                           Predicate.single
                             (Some (MS_val_spec
                                     (Stringa.explode f, mk_x Arith.Zero_nat,
                                       ba, ca, ta))))
                  | (_, SailAST.DEF_spec
                          (SailAST.VS_aux
                            (SailAST.TypSchm_ts (_, _),
                              (SailAST.Operator _, _))))
                    -> Predicate.bot_pred
                  | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_loop_measures (_, _)) ->
                      Predicate.bot_pred
                    | (_, SailAST.DEF_reg_dec
                            (SailAST.DEC_reg (_, _, _, typ, _)))
                      -> Predicate.bind (t_conv_i_i_o [] typ)
                           (fun xb ->
                             Predicate.bind (eq_o_i (mk_u Arith.Zero_nat))
                               (fun xaa ->
                                 Predicate.bind
                                   (eq_o_i (Syntax.V_lit (Syntax.L_bitvec [])))
                                   (fun xba ->
                                     Predicate.single
                                       (Some (MS_register (xaa, xb, xba))))))
                    | (_, SailAST.DEF_reg_dec (SailAST.DEC_config (_, _, _, _)))
                      -> Predicate.bot_pred
                    | (_, SailAST.DEF_reg_dec (SailAST.DEC_alias (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, SailAST.DEF_reg_dec
                            (SailAST.DEC_typ_alias (_, _, _, _)))
                      -> Predicate.bot_pred
                    | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.DEF_overload (_, _)) ->
                        Predicate.single None
                      | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.DEF_loop_measures (_, _)) ->
                        Predicate.bot_pred
                      | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a
                        with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_fixity (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                        | (_, SailAST.DEF_default _) -> Predicate.single None
                        | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_measure (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_loop_measures (_, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_internal_mutrec _) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_pragma (_, _)) ->
                          Predicate.bot_pred)))
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a
                        with (_, SailAST.DEF_type
                                   (SailAST.TD_aux
                                     (SailAST.TD_abbrev (_, _, _))))
                          -> Predicate.single None
                        | (_, SailAST.DEF_type
                                (SailAST.TD_aux
                                  (SailAST.TD_record (_, _, _, _))))
                          -> Predicate.bot_pred
                        | (_, SailAST.DEF_type
                                (SailAST.TD_aux
                                  (SailAST.TD_variant (_, _, _, _))))
                          -> Predicate.bot_pred
                        | (_, SailAST.DEF_type
                                (SailAST.TD_aux (SailAST.TD_enum (_, _, _))))
                          -> Predicate.bot_pred
                        | (_, SailAST.DEF_type
                                (SailAST.TD_aux
                                  (SailAST.TD_bitfield (_, _, _))))
                          -> Predicate.bot_pred
                        | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_fixity (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                        | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_measure (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_loop_measures (_, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_internal_mutrec _) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_pragma (_, _)) ->
                          Predicate.bot_pred)))))))));;

end;; (*struct SailToMs*)

module Validator : sig
  val mk_id : Stringa.char list -> SailAST.id
  val nc_or :
    SailAST.n_constraint -> SailAST.n_constraint -> SailAST.n_constraint
  val trace : Stringa.char list -> bool
  val env_of :
    (unit Env.tannot_ext option) SailAST.exp -> unit Env.env_ext option
  val eq_i_i : 'a HOL.equal -> 'a -> 'a -> unit Predicate.pred
  val eq_o_i : 'a -> 'a Predicate.pred
  val nc_and :
    SailAST.n_constraint -> SailAST.n_constraint -> SailAST.n_constraint
  val arg_bool : SailAST.n_constraint -> SailAST.typ_arg
  val nc_not : SailAST.n_constraint -> SailAST.n_constraint
  val integer_of_int2 : Arith.int -> Z.t
  val check_lit_i_i_i :
    unit Env.env_ext -> SailAST.lit -> SailAST.typ -> unit Predicate.pred
  val normalise_i_i_o :
    unit Env.env_ext -> SailAST.typ -> SailAST.typ Predicate.pred
  val nc_and_list : SailAST.n_constraint list -> SailAST.n_constraint
  val match_nexp_i_i_o :
    SailAST.nexp -> SailAST.nexp -> (SailAST.n_constraint list) Predicate.pred
  val nc_bool_equiv :
    SailAST.n_constraint -> SailAST.n_constraint -> SailAST.n_constraint
  val match_nc_i_i_o :
    SailAST.n_constraint ->
      SailAST.n_constraint -> (SailAST.n_constraint list) Predicate.pred
  val nc_between :
    SailAST.nexp -> SailAST.nexp -> SailAST.nexp -> SailAST.n_constraint
  val eq_kid_i_i : SailAST.kid -> SailAST.kid -> unit Predicate.pred
  val eq_id_i_i : SailAST.id -> SailAST.id -> unit Predicate.pred
  val match_i_i_o :
    SailAST.typ -> SailAST.typ -> (SailAST.n_constraint list) Predicate.pred
  val match_arg_i_i_o :
    SailAST.typ_arg ->
      SailAST.typ_arg -> (SailAST.n_constraint list) Predicate.pred
  val match_arg_list_i_i_o :
    SailAST.typ_arg list ->
      SailAST.typ_arg list -> (SailAST.n_constraint list) Predicate.pred
  val match_list_i_i_o :
    SailAST.typ list ->
      SailAST.typ list -> (SailAST.n_constraint list) Predicate.pred
  val subtype_i_i_i :
    unit Env.env_ext -> SailAST.typ -> SailAST.typ -> unit Predicate.pred
  val check_pat_i_o :
    (unit Env.tannot_ext option) SailAST.pat ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val check_pat_list_i_o :
    (unit Env.tannot_ext option) SailAST.pat list ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val subenv_i_i : unit Env.env_ext -> unit Env.env_ext -> unit Predicate.pred
  val locals_in :
    unit Env.env_ext -> (SailAST.id * (Env.mut * SailAST.typ)) list -> bool
  val check_local_binds_i_i :
    (unit Env.tannot_ext option) SailAST.exp list ->
      (SailAST.id * (Env.mut * SailAST.typ)) list -> unit Predicate.pred
  val subtype_exp_i_i :
    (unit Env.tannot_ext option) SailAST.exp ->
      SailAST.typ -> unit Predicate.pred
  val subtype_tan_i_i :
    SailAST.typ -> unit Env.tannot_ext option -> unit Predicate.pred
  val check_lexp_vector_list_i_i_i :
    (unit Env.tannot_ext option) SailAST.lexp list ->
      SailAST.order -> SailAST.typ -> unit Predicate.pred
  val add_locals :
    unit Env.env_ext ->
      (SailAST.id * (Env.mut * SailAST.typ)) list -> unit Env.env_ext
  val check_letbind_i_o :
    (unit Env.tannot_ext option) SailAST.letbind ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val check_exp_i_o :
    (unit Env.tannot_ext option) SailAST.exp ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val check_pexp_i :
    (unit Env.tannot_ext option) SailAST.pexp -> unit Predicate.pred
  val check_pexps_i :
    (unit Env.tannot_ext option) SailAST.pexp list -> unit Predicate.pred
  val check_exp_typ_i_i :
    (unit Env.tannot_ext option) SailAST.exp ->
      SailAST.typ -> unit Predicate.pred
  val check_fexp_i_i :
    (unit Env.tannot_ext option) SailAST.fexp ->
      SailAST.typ -> unit Predicate.pred
  val check_fexp_list_i_i :
    (unit Env.tannot_ext option) SailAST.fexp list ->
      SailAST.typ -> unit Predicate.pred
  val check_lexp_i_o :
    (unit Env.tannot_ext option) SailAST.lexp ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val check_lexp_list_i_o :
    (unit Env.tannot_ext option) SailAST.lexp list ->
      ((SailAST.id * (Env.mut * SailAST.typ)) list) Predicate.pred
  val check_exp_list_i_i :
    (unit Env.tannot_ext option) SailAST.exp list ->
      SailAST.typ list -> unit Predicate.pred
  val check_exp_typ_env_i_i_i :
    unit Env.env_ext ->
      (unit Env.tannot_ext option) SailAST.exp ->
        SailAST.typ -> unit Predicate.pred
  val check_funcls_i_i :
    (unit Env.tannot_ext option) SailAST.funcl list ->
      SailAST.tannot_opt -> unit Predicate.pred
  val check_sd_i_i :
    unit Env.env_ext ->
      (unit Env.tannot_ext option) SailAST.scattered_def -> unit Predicate.pred
  val check_def_i_i :
    unit Env.env_ext ->
      (unit Env.tannot_ext option) SailAST.def -> unit Predicate.pred
  val check_def :
    unit Env.env_ext -> (unit Env.tannot_ext option) SailAST.def -> bool
end = struct

let rec mk_id x = SailAST.Id (Stringa.implode x);;

let rec nc_or nc1 nc2 = SailAST.NC_or (nc1, nc2);;

let rec trace s = (let _ = Utils2.trace (Stringa.implode s) in true);;

let rec env_of exp = Env.get_env (SailAST.annot_e exp);;

let rec eq_i_i _A
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (x, xaa) ->
        (if HOL.eq _A x xaa then Predicate.single () else Predicate.bot_pred));;

let rec eq_o_i xa = Predicate.bind (Predicate.single xa) Predicate.single;;

let rec nc_and nc1 nc2 = SailAST.NC_and (nc1, nc2);;

let rec arg_bool nc = SailAST.A_bool nc;;

let rec nc_not
  nc = SailAST.NC_app
         (mk_id [Stringa.Chara
                   (false, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (true, true, true, true, false, true, true, false);
                  Stringa.Chara
                    (false, false, true, false, true, true, true, false)],
           [arg_bool nc]);;

let rec integer_of_int2 x = Arith.integer_of_int x;;

let rec check_lit_i_i_i
  x xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xa, xb)))
        (fun a ->
          (match a
            with (_, (SailAST.L_unit, SailAST.Typ_internal_unknown)) ->
              Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_id (SailAST.Id xc))) ->
              (if ((xc : string) = "unit") then Predicate.single ()
                else Predicate.bot_pred)
            | (_, (SailAST.L_unit, SailAST.Typ_id (SailAST.Operator _))) ->
              Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_var _)) -> Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_fn (_, _, _))) ->
              Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_bidir (_, _, _))) ->
              Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_tup _)) -> Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_app (_, _))) ->
              Predicate.bot_pred
            | (_, (SailAST.L_unit, SailAST.Typ_exist (_, _, _))) ->
              Predicate.bot_pred
            | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
            | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, (xa, xb)))
          (fun a ->
            (match a with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_internal_unknown)) ->
                Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_id _)) -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_var _)) -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_fn (_, _, _))) ->
                Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_bidir (_, _, _))) ->
                Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_tup _)) -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_app (SailAST.Id _, []))) ->
                Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_id _) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_var _) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num num,
                      SailAST.Typ_app
                        (SailAST.Id xc,
                          [SailAST.A_nexp (SailAST.Nexp_constant numa)])))
                -> (if Z.equal num numa && ((xc : string) = "atom")
                     then Predicate.single () else Predicate.bot_pred)
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_constant _) :: _ :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_app (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_times (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_sum (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_minus (_, _)) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_exp _) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app
                        (SailAST.Id _,
                          SailAST.A_nexp (SailAST.Nexp_neg _) :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _,
                      SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_app (SailAST.Operator _, _)))
                -> Predicate.bot_pred
              | (_, (SailAST.L_num _, SailAST.Typ_exist (_, _, _))) ->
                Predicate.bot_pred
              | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
              | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, (xa, xb)))
            (fun a ->
              (match a with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_internal_unknown)) ->
                  Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_id _)) -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_var _)) -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_fn (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_bidir (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_tup _)) -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_app (SailAST.Id _, []))) ->
                  Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app (SailAST.Id _, SailAST.A_nexp _ :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_equal (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_bounded_ge (_, _)) ::
                              _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_bounded_gt (_, _)) ::
                              _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_bounded_le (_, _)) ::
                              _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_bounded_lt (_, _)) ::
                              _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_not_equal (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_set (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_or (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_and (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_app (_, _)) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool (SailAST.NC_var _) :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id xc, [SailAST.A_bool SailAST.NC_true])))
                  -> (if ((xc : string) = "atom_bool") then Predicate.single ()
                       else Predicate.bot_pred)
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _,
                            SailAST.A_bool SailAST.NC_true :: _ :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true,
                        SailAST.Typ_app
                          (SailAST.Id _, SailAST.A_bool SailAST.NC_false :: _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_app (SailAST.Operator _, _)))
                  -> Predicate.bot_pred
                | (_, (SailAST.L_true, SailAST.Typ_exist (_, _, _))) ->
                  Predicate.bot_pred
                | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, (xa, xb)))
              (fun a ->
                (match a with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_internal_unknown)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_id _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_var _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_fn (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_bidir (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_tup _)) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_app (SailAST.Id _, [])))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _, SailAST.A_nexp _ :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _, SailAST.A_order _ :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_equal (_, _)) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_bounded_ge (_, _)) ::
                                _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_bounded_gt (_, _)) ::
                                _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_bounded_le (_, _)) ::
                                _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_bounded_lt (_, _)) ::
                                _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_not_equal (_, _)) ::
                                _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_set (_, _)) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_or (_, _)) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_and (_, _)) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_app (_, _)) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool (SailAST.NC_var _) :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool SailAST.NC_true :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id xc, [SailAST.A_bool SailAST.NC_false])))
                    -> (if ((xc : string) = "atom_bool")
                         then Predicate.single () else Predicate.bot_pred)
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app
                            (SailAST.Id _,
                              SailAST.A_bool SailAST.NC_false :: _ :: _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false,
                          SailAST.Typ_app (SailAST.Operator _, _)))
                    -> Predicate.bot_pred
                  | (_, (SailAST.L_false, SailAST.Typ_exist (_, _, _))) ->
                    Predicate.bot_pred
                  | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                  | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, (xa, xb)))
                (fun a ->
                  (match a with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_internal_unknown)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_id (SailAST.Id xc))) ->
                      (if ((xc : string) = "bit") then Predicate.single ()
                        else Predicate.bot_pred)
                    | (_, (SailAST.L_one, SailAST.Typ_id (SailAST.Operator _)))
                      -> Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_var _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_fn (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_bidir (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_tup _)) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_app (_, _))) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_one, SailAST.Typ_exist (_, _, _))) ->
                      Predicate.bot_pred
                    | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                    | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, (xa, xb)))
                  (fun a ->
                    (match a with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_internal_unknown)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_id (SailAST.Id xc))) ->
                        (if ((xc : string) = "bit") then Predicate.single ()
                          else Predicate.bot_pred)
                      | (_, (SailAST.L_zero,
                              SailAST.Typ_id (SailAST.Operator _)))
                        -> Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_var _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_fn (_, _, _))) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_bidir (_, _, _))) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_tup _)) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_app (_, _))) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_zero, SailAST.Typ_exist (_, _, _))) ->
                        Predicate.bot_pred
                      | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                      | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, (xa, xb)))
                    (fun a ->
                      (match a
                        with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_internal_unknown))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_id _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_var _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_fn (_, _, _))) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_bidir (_, _, _))) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_tup _)) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app (SailAST.Id _, [])))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_id _) :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_var _) :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    [SailAST.A_nexp
                                       (SailAST.Nexp_constant _)])))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_constant _) ::
                                      SailAST.A_nexp _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_constant _) ::
                                      SailAST.A_typ _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin s,
                                SailAST.Typ_app
                                  (SailAST.Id xc,
                                    [SailAST.A_nexp (SailAST.Nexp_constant xaa);
                                      SailAST.A_order _])))
                          -> (if Z.equal xaa
                                   (integer_of_int2
                                     (Arith.of_nat Arith.semiring_1_int
                                       (Lista.size_list
 (Stringa.explode s)))) &&
                                   ((xc : string) = "bitvector")
                               then Predicate.single () else Predicate.bot_pred)
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_constant _) ::
                                      SailAST.A_order _ :: _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_constant _) ::
                                      SailAST.A_bool _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_app (_, _)) ::
                                      _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp
                                      (SailAST.Nexp_times (_, _)) ::
                                      _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_sum (_, _)) ::
                                      _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp
                                      (SailAST.Nexp_minus (_, _)) ::
                                      _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_exp _) :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _,
                                    SailAST.A_nexp (SailAST.Nexp_neg _) :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _, SailAST.A_typ _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _, SailAST.A_order _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app
                                  (SailAST.Id _, SailAST.A_bool _ :: _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _,
                                SailAST.Typ_app (SailAST.Operator _, _)))
                          -> Predicate.bot_pred
                        | (_, (SailAST.L_bin _, SailAST.Typ_exist (_, _, _))) ->
                          Predicate.bot_pred
                        | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                        | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, (xa, xb)))
                      (fun a ->
                        (match a
                          with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_internal_unknown))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_id _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_var _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_fn (_, _, _))) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_bidir (_, _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_tup _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app (SailAST.Id _, [])))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp (SailAST.Nexp_id _) :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp (SailAST.Nexp_var _) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      [SailAST.A_nexp
 (SailAST.Nexp_constant _)])))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_constant _) ::
SailAST.A_nexp _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_constant _) ::
SailAST.A_typ _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex s,
                                  SailAST.Typ_app
                                    (SailAST.Id xc,
                                      [SailAST.A_nexp
 (SailAST.Nexp_constant xaa);
SailAST.A_order _])))
                            -> (if Z.equal xaa
                                     (Z.mul (Z.of_int 4)
                                       (integer_of_int2
 (Arith.of_nat Arith.semiring_1_int (Lista.size_list (Stringa.explode s))))) &&
                                     ((xc : string) = "bitvector")
                                 then Predicate.single ()
                                 else Predicate.bot_pred)
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_constant _) ::
SailAST.A_order _ :: _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_constant _) ::
SailAST.A_bool _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_app (_, _)) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_times (_, _)) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_sum (_, _)) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp
(SailAST.Nexp_minus (_, _)) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp (SailAST.Nexp_exp _) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _,
                                      SailAST.A_nexp (SailAST.Nexp_neg _) ::
_)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _, SailAST.A_typ _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _, SailAST.A_order _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app
                                    (SailAST.Id _, SailAST.A_bool _ :: _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _,
                                  SailAST.Typ_app (SailAST.Operator _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _, SailAST.Typ_exist (_, _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_string _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_real _, _)) -> Predicate.bot_pred)))
                    (Predicate.bind (Predicate.single (x, (xa, xb)))
                      (fun a ->
                        (match a
                          with (_, (SailAST.L_unit, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_zero, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_one, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_true, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_false, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_num _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_hex _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_bin _, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_string _,
                                  SailAST.Typ_internal_unknown))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_string _,
                                  SailAST.Typ_id (SailAST.Id xc)))
                            -> (if ((xc : string) = "string")
                                 then Predicate.single ()
                                 else Predicate.bot_pred)
                          | (_, (SailAST.L_string _,
                                  SailAST.Typ_id (SailAST.Operator _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_string _, SailAST.Typ_var _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_string _, SailAST.Typ_fn (_, _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_string _,
                                  SailAST.Typ_bidir (_, _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_string _, SailAST.Typ_tup _)) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_string _, SailAST.Typ_app (_, _))) ->
                            Predicate.bot_pred
                          | (_, (SailAST.L_string _,
                                  SailAST.Typ_exist (_, _, _)))
                            -> Predicate.bot_pred
                          | (_, (SailAST.L_undef, _)) -> Predicate.bot_pred
                          | (_, (SailAST.L_real _, _)) ->
                            Predicate.bot_pred))))))))));;

let rec normalise_i_i_o
  xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (xa, xb))
        (fun a ->
          (match a with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
            | (_, SailAST.Typ_id _) -> Predicate.bot_pred
            | (_, SailAST.Typ_var _) -> Predicate.bot_pred
            | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
            | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
            | (_, SailAST.Typ_exist (x, y, z)) ->
              Predicate.single (SailAST.Typ_exist (x, y, z)))))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (xa, xb))
          (fun a ->
            (match a
              with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
              | (_, SailAST.Typ_id i) ->
                Predicate.single
                  (SailAST.Typ_exist ([], SailAST.NC_true, SailAST.Typ_id i))
              | (_, SailAST.Typ_var _) -> Predicate.bot_pred
              | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
              | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
              | (_, SailAST.Typ_exist (_, _, _)) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (xa, xb))
            (fun a ->
              (match a
                with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
                | (_, SailAST.Typ_id _) -> Predicate.bot_pred
                | (_, SailAST.Typ_var k) ->
                  Predicate.single
                    (SailAST.Typ_exist ([], SailAST.NC_true, SailAST.Typ_var k))
                | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
                | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
                | (_, SailAST.Typ_exist (_, _, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (xa, xb))
              (fun a ->
                (match a
                  with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
                  | (_, SailAST.Typ_id _) -> Predicate.bot_pred
                  | (_, SailAST.Typ_var _) -> Predicate.bot_pred
                  | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.Typ_tup ts) ->
                    Predicate.single
                      (SailAST.Typ_exist
                        ([], SailAST.NC_true, SailAST.Typ_tup ts))
                  | (_, SailAST.Typ_app (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.Typ_exist (_, _, _)) -> Predicate.bot_pred)))
            (Predicate.bind (Predicate.single (xa, xb))
              (fun a ->
                (match a
                  with (_, SailAST.Typ_internal_unknown) -> Predicate.bot_pred
                  | (_, SailAST.Typ_id _) -> Predicate.bot_pred
                  | (_, SailAST.Typ_var _) -> Predicate.bot_pred
                  | (_, SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.Typ_bidir (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.Typ_tup _) -> Predicate.bot_pred
                  | (_, SailAST.Typ_app (idd, tas)) ->
                    Predicate.single
                      (SailAST.Typ_exist
                        ([], SailAST.NC_true, SailAST.Typ_app (idd, tas)))
                  | (_, SailAST.Typ_exist (_, _, _)) ->
                    Predicate.bot_pred))))));;

let rec nc_and_list ncs = Lista.fold nc_and ncs SailAST.NC_true;;

let rec match_nexp_i_i_o
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun (ne1, ne2) -> Predicate.single [SailAST.NC_equal (ne1, ne2)]);;

let rec nc_bool_equiv
  nc1 nc2 = nc_or (nc_and nc1 nc2) (nc_and (nc_not nc1) (nc_not nc2));;

let rec match_nc_i_i_o
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun (nc1, nc2) -> Predicate.single [nc_bool_equiv nc1 nc2]);;

let rec nc_between
  n1 n n2 =
    nc_and (SailAST.NC_bounded_le (n1, n)) (SailAST.NC_bounded_ge (n, n1));;

let rec eq_kid_i_i
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (SailAST.Var _, SailAST.Var _) -> Predicate.single ());;

let rec eq_id_i_i
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun a ->
        (match a with (SailAST.Id _, SailAST.Id _) -> Predicate.single ()
          | (SailAST.Id _, SailAST.Operator _) -> Predicate.bot_pred
          | (SailAST.Operator _, _) -> Predicate.bot_pred));;

let rec match_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (SailAST.Typ_internal_unknown, _) -> Predicate.bot_pred
            | (SailAST.Typ_id _, _) -> Predicate.bot_pred
            | (SailAST.Typ_var _, _) -> Predicate.bot_pred
            | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
            | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
            | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_internal_unknown) ->
              Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_id _) -> Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_var _) -> Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_fn (_, _, _)) ->
              Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_bidir (_, _, _)) ->
              Predicate.bot_pred
            | (SailAST.Typ_app (_, _), SailAST.Typ_tup _) -> Predicate.bot_pred
            | (SailAST.Typ_app (id1, args1), SailAST.Typ_app (id2, args2)) ->
              Predicate.bind (eq_id_i_i id1 id2)
                (fun () ->
                  Predicate.bind (match_arg_list_i_i_o args1 args2)
                    Predicate.single)
            | (SailAST.Typ_app (_, _), SailAST.Typ_exist (_, _, _)) ->
              Predicate.bot_pred
            | (SailAST.Typ_exist (_, _, _), _) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a
              with (SailAST.Typ_internal_unknown, _) -> Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_internal_unknown) ->
                Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_id _) -> Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_var _) -> Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_fn (_, _, _)) ->
                Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_bidir (_, _, _)) ->
                Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_tup _) -> Predicate.bot_pred
              | (SailAST.Typ_id id1, SailAST.Typ_app (id2, [])) ->
                Predicate.bind (eq_id_i_i id1 id2)
                  (fun () -> Predicate.single [])
              | (SailAST.Typ_id _, SailAST.Typ_app (_, _ :: _)) ->
                Predicate.bot_pred
              | (SailAST.Typ_id _, SailAST.Typ_exist (_, _, _)) ->
                Predicate.bot_pred
              | (SailAST.Typ_var _, _) -> Predicate.bot_pred
              | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
              | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
              | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
              | (SailAST.Typ_app (_, _), _) -> Predicate.bot_pred
              | (SailAST.Typ_exist (_, _, _), _) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a
                with (SailAST.Typ_internal_unknown, _) -> Predicate.bot_pred
                | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
                | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_internal_unknown) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (id1, []), SailAST.Typ_id id2) ->
                  Predicate.bind (eq_id_i_i id1 id2)
                    (fun () -> Predicate.single [])
                | (SailAST.Typ_app (_, []), SailAST.Typ_var _) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_fn (_, _, _)) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_bidir (_, _, _)) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_tup _) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_app (_, _)) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, []), SailAST.Typ_exist (_, _, _)) ->
                  Predicate.bot_pred
                | (SailAST.Typ_app (_, _ :: _), _) -> Predicate.bot_pred
                | (SailAST.Typ_exist (_, _, _), _) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a
                  with (SailAST.Typ_internal_unknown, _) -> Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_internal_unknown) ->
                    Predicate.bot_pred
                  | (SailAST.Typ_id id1, SailAST.Typ_id id2) ->
                    Predicate.bind (eq_id_i_i id1 id2)
                      (fun () -> Predicate.single [])
                  | (SailAST.Typ_id _, SailAST.Typ_var _) -> Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_fn (_, _, _)) ->
                    Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_bidir (_, _, _)) ->
                    Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_tup _) -> Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_app (_, _)) ->
                    Predicate.bot_pred
                  | (SailAST.Typ_id _, SailAST.Typ_exist (_, _, _)) ->
                    Predicate.bot_pred
                  | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                  | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                  | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
                  | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                  | (SailAST.Typ_app (_, _), _) -> Predicate.bot_pred
                  | (SailAST.Typ_exist (_, _, _), _) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a
                    with (SailAST.Typ_internal_unknown, _) -> Predicate.bot_pred
                    | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_internal_unknown) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_id _) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var kid1, SailAST.Typ_var kid2) ->
                      Predicate.bind (eq_kid_i_i kid1 kid2)
                        (fun () -> Predicate.single [])
                    | (SailAST.Typ_var _, SailAST.Typ_fn (_, _, _)) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_bidir (_, _, _)) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_tup _) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_app (_, _)) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_var _, SailAST.Typ_exist (_, _, _)) ->
                      Predicate.bot_pred
                    | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                    | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
                    | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                    | (SailAST.Typ_app (_, _), _) -> Predicate.bot_pred
                    | (SailAST.Typ_exist (_, _, _), _) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a
                      with (SailAST.Typ_internal_unknown, _) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                      | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                      | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                      | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_internal_unknown) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_id _) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_var _) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_fn (_, _, _)) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_bidir (_, _, _)) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup ts1, SailAST.Typ_tup ts2) ->
                        Predicate.bind (match_list_i_i_o ts1 ts2)
                          Predicate.single
                      | (SailAST.Typ_tup _, SailAST.Typ_app (_, _)) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_tup _, SailAST.Typ_exist (_, _, _)) ->
                        Predicate.bot_pred
                      | (SailAST.Typ_app (_, _), _) -> Predicate.bot_pred
                      | (SailAST.Typ_exist (_, _, _), _) ->
                        Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a
                        with (SailAST.Typ_internal_unknown, _) ->
                          Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _),
                            SailAST.Typ_internal_unknown)
                          -> Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _), SailAST.Typ_id _) ->
                          Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _), SailAST.Typ_var _) ->
                          Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _),
                            SailAST.Typ_fn (_, _, _))
                          -> Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _),
                            SailAST.Typ_bidir (_, _, _))
                          -> Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _), SailAST.Typ_tup _) ->
                          Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id xb),
                            SailAST.Typ_app (SailAST.Id xaa, _))
                          -> (if ((xaa : string) = "atom") &&
                                   ((xb : string) = "int")
                               then Predicate.single [] else Predicate.bot_pred)
                        | (SailAST.Typ_id (SailAST.Id _),
                            SailAST.Typ_app (SailAST.Operator _, _))
                          -> Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Id _),
                            SailAST.Typ_exist (_, _, _))
                          -> Predicate.bot_pred
                        | (SailAST.Typ_id (SailAST.Operator _), _) ->
                          Predicate.bot_pred
                        | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                        | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                        | (SailAST.Typ_bidir (_, _, _), _) -> Predicate.bot_pred
                        | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                        | (SailAST.Typ_app (_, _), _) -> Predicate.bot_pred
                        | (SailAST.Typ_exist (_, _, _), _) ->
                          Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, xa))
                      (fun a ->
                        (match a
                          with (SailAST.Typ_internal_unknown, _) ->
                            Predicate.bot_pred
                          | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                          | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                          | (SailAST.Typ_fn (_, _, _), _) -> Predicate.bot_pred
                          | (SailAST.Typ_bidir (_, _, _), _) ->
                            Predicate.bot_pred
                          | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_internal_unknown)
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id xb, _),
                              SailAST.Typ_id (SailAST.Id xaa))
                            -> (if ((xaa : string) = "int") &&
                                     ((xb : string) = "atom")
                                 then Predicate.single [SailAST.NC_true]
                                 else Predicate.bot_pred)
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_id (SailAST.Operator _))
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_var _)
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_fn (_, _, _))
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_bidir (_, _, _))
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_tup _)
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_app (_, _))
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Id _, _),
                              SailAST.Typ_exist (_, _, _))
                            -> Predicate.bot_pred
                          | (SailAST.Typ_app (SailAST.Operator _, _), _) ->
                            Predicate.bot_pred
                          | (SailAST.Typ_exist (_, _, _), _) ->
                            Predicate.bot_pred)))
                    (Predicate.sup_pred
                      (Predicate.bind (Predicate.single (x, xa))
                        (fun a ->
                          (match a
                            with (SailAST.Typ_internal_unknown, _) ->
                              Predicate.bot_pred
                            | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                            | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                            | (SailAST.Typ_fn (_, _, _), _) ->
                              Predicate.bot_pred
                            | (SailAST.Typ_bidir (_, _, _), _) ->
                              Predicate.bot_pred
                            | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                            | (SailAST.Typ_app (SailAST.Id _, []), _) ->
                              Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_internal_unknown)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id xb, [SailAST.A_nexp nexp]),
                                SailAST.Typ_id (SailAST.Id xaa))
                              -> (if ((xaa : string) = "nat") &&
                                       ((xb : string) = "atom")
                                   then Predicate.single
  [SailAST.NC_bounded_ge (nexp, SailAST.Nexp_constant Z.zero)]
                                   else Predicate.bot_pred)
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_id (SailAST.Operator _))
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_var _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_fn (_, _, _))
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_bidir (_, _, _))
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_tup _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_app (_, _))
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, [SailAST.A_nexp _]),
                                SailAST.Typ_exist (_, _, _))
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_nexp _ :: _ :: _),
                                _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_typ _ :: _),
                                _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_order _ :: _),
                                _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app
                                 (SailAST.Id _, SailAST.A_bool _ :: _),
                                _)
                              -> Predicate.bot_pred
                            | (SailAST.Typ_app (SailAST.Operator _, _), _) ->
                              Predicate.bot_pred
                            | (SailAST.Typ_exist (_, _, _), _) ->
                              Predicate.bot_pred)))
                      (Predicate.sup_pred
                        (Predicate.bind (Predicate.single (x, xa))
                          (fun a ->
                            (match a
                              with (SailAST.Typ_internal_unknown, _) ->
                                Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_internal_unknown)
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_id _)
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_var _)
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_fn (_, _, _))
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_bidir (_, _, _))
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_tup _)
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id xb),
                                  SailAST.Typ_app (SailAST.Id xaa, _))
                                -> (if ((xaa : string) = "atom") &&
 ((xb : string) = "nat")
                                     then Predicate.single []
                                     else Predicate.bot_pred)
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_app (SailAST.Operator _, _))
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Id _),
                                  SailAST.Typ_exist (_, _, _))
                                -> Predicate.bot_pred
                              | (SailAST.Typ_id (SailAST.Operator _), _) ->
                                Predicate.bot_pred
                              | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                              | (SailAST.Typ_fn (_, _, _), _) ->
                                Predicate.bot_pred
                              | (SailAST.Typ_bidir (_, _, _), _) ->
                                Predicate.bot_pred
                              | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                              | (SailAST.Typ_app (_, _), _) ->
                                Predicate.bot_pred
                              | (SailAST.Typ_exist (_, _, _), _) ->
                                Predicate.bot_pred)))
                        (Predicate.sup_pred
                          (Predicate.bind (Predicate.single (x, xa))
                            (fun a ->
                              (match a
                                with (SailAST.Typ_internal_unknown, _) ->
                                  Predicate.bot_pred
                                | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                                | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                                | (SailAST.Typ_fn (_, _, _), _) ->
                                  Predicate.bot_pred
                                | (SailAST.Typ_bidir (_, _, _), _) ->
                                  Predicate.bot_pred
                                | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                                | (SailAST.Typ_app (SailAST.Id _, []), _) ->
                                  Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_internal_unknown)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_id _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_var _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_fn (_, _, _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_bidir (_, _, _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_tup _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app (SailAST.Id _, []))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _, [SailAST.A_nexp _]))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id xb, [SailAST.A_nexp ne]),
                                    SailAST.Typ_app
                                      (SailAST.Id xaa,
[SailAST.A_nexp ne1; SailAST.A_nexp ne2]))
                                  -> (if ((xaa : string) = "range") &&
   ((xb : string) = "atom")
                                       then Predicate.single
      [nc_between ne1 ne ne2]
                                       else Predicate.bot_pred)
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _,
SailAST.A_nexp _ :: SailAST.A_nexp _ :: _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _,
SailAST.A_nexp _ :: SailAST.A_typ _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _,
SailAST.A_nexp _ :: SailAST.A_order _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _,
SailAST.A_nexp _ :: SailAST.A_bool _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _, SailAST.A_typ _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _, SailAST.A_order _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app
                                      (SailAST.Id _, SailAST.A_bool _ :: _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_app (SailAST.Operator _, _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, [SailAST.A_nexp _]),
                                    SailAST.Typ_exist (_, _, _))
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, SailAST.A_nexp _ :: _ :: _),
                                    _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, SailAST.A_typ _ :: _),
                                    _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, SailAST.A_order _ :: _),
                                    _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app
                                     (SailAST.Id _, SailAST.A_bool _ :: _),
                                    _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_app (SailAST.Operator _, _), _)
                                  -> Predicate.bot_pred
                                | (SailAST.Typ_exist (_, _, _), _) ->
                                  Predicate.bot_pred)))
                          (Predicate.sup_pred
                            (Predicate.bind (Predicate.single (x, xa))
                              (fun a ->
                                (match a
                                  with (SailAST.Typ_internal_unknown, _) ->
                                    Predicate.bot_pred
                                  | (SailAST.Typ_id _, _) -> Predicate.bot_pred
                                  | (SailAST.Typ_var _, _) -> Predicate.bot_pred
                                  | (SailAST.Typ_fn (_, _, _), _) ->
                                    Predicate.bot_pred
                                  | (SailAST.Typ_bidir (_, _, _), _) ->
                                    Predicate.bot_pred
                                  | (SailAST.Typ_tup _, _) -> Predicate.bot_pred
                                  | (SailAST.Typ_app (SailAST.Id _, []), _) ->
                                    Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _, [SailAST.A_nexp _]),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_internal_unknown)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_id _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_var _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_fn (_, _, _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_bidir (_, _, _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_tup _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app (SailAST.Id _, []))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id xb,
 [SailAST.A_nexp ne1; SailAST.A_nexp ne2]),
                                      SailAST.Typ_app
(SailAST.Id xaa, [SailAST.A_nexp ne]))
                                    -> (if ((xaa : string) = "atom") &&
     ((xb : string) = "range")
 then Predicate.single [nc_between ne1 ne ne2] else Predicate.bot_pred)
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app
(SailAST.Id _, SailAST.A_nexp _ :: _ :: _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app
(SailAST.Id _, SailAST.A_typ _ :: _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app
(SailAST.Id _, SailAST.A_order _ :: _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app
(SailAST.Id _, SailAST.A_bool _ :: _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_app (SailAST.Operator _, _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 [SailAST.A_nexp _; SailAST.A_nexp _]),
                                      SailAST.Typ_exist (_, _, _))
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 SailAST.A_nexp _ :: SailAST.A_nexp _ :: _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 SailAST.A_nexp _ :: SailAST.A_typ _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 SailAST.A_nexp _ :: SailAST.A_order _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _,
 SailAST.A_nexp _ :: SailAST.A_bool _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _, SailAST.A_typ _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _, SailAST.A_order _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app
                                       (SailAST.Id _, SailAST.A_bool _ :: _),
                                      _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_app (SailAST.Operator _, _), _)
                                    -> Predicate.bot_pred
                                  | (SailAST.Typ_exist (_, _, _), _) ->
                                    Predicate.bot_pred)))
                            (Predicate.sup_pred
                              (Predicate.bind (Predicate.single (x, xa))
                                (fun a ->
                                  (match a
                                    with (SailAST.Typ_internal_unknown, _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_id _, _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_var _, _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_fn (_, _, _), _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_bidir (_, _, _), _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_tup _, _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_app (SailAST.Id _, []), _) ->
                                      Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _]),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_internal_unknown)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id xb, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_id (SailAST.Id xaa))
                                      -> (if ((xaa : string) = "int") &&
       ((xb : string) = "range")
   then Predicate.single [SailAST.NC_true] else Predicate.bot_pred)
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_id (SailAST.Operator _))
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_var _)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_fn (_, _, _))
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_bidir (_, _, _))
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_tup _)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_app (_, _))
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, [SailAST.A_nexp _; SailAST.A_nexp _]),
SailAST.Typ_exist (_, _, _))
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_nexp _ :: _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_typ _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_order _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_nexp _ :: SailAST.A_bool _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_typ _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_order _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app
 (SailAST.Id _, SailAST.A_bool _ :: _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_app (SailAST.Operator _, _),
_)
                                      -> Predicate.bot_pred
                                    | (SailAST.Typ_exist (_, _, _), _) ->
                                      Predicate.bot_pred)))
                              (Predicate.sup_pred
                                (Predicate.bind (Predicate.single (x, xa))
                                  (fun a ->
                                    (match a
                                      with (SailAST.Typ_internal_unknown, _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_id _, _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_var _, _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_fn (_, _, _), _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_bidir (_, _, _), _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_tup _, _) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_internal_unknown) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id xb, _), SailAST.Typ_id (SailAST.Id xaa)) ->
(if ((xaa : string) = "bool") && ((xb : string) = "atom_bool")
  then Predicate.single [SailAST.NC_true] else Predicate.bot_pred)
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_id (SailAST.Operator _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_var _) -> Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_fn (_, _, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_bidir (_, _, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_tup _) -> Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_app (_, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Id _, _), SailAST.Typ_exist (_, _, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_app (SailAST.Operator _, _), _) -> Predicate.bot_pred
                                      | (SailAST.Typ_exist (_, _, _), _) ->
Predicate.bot_pred)))
                                (Predicate.bind (Predicate.single (x, xa))
                                  (fun a ->
                                    (match a
                                      with (SailAST.Typ_internal_unknown, _) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_internal_unknown) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_id _) -> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_var _) -> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_fn (_, _, _)) -> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_bidir (_, _, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_tup _) -> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_app (SailAST.Id _, [])) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _),
  SailAST.Typ_app (SailAST.Id _, SailAST.A_nexp _ :: _))
-> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _),
  SailAST.Typ_app (SailAST.Id _, SailAST.A_typ _ :: _))
-> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _),
  SailAST.Typ_app (SailAST.Id _, SailAST.A_order _ :: _))
-> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id xb),
  SailAST.Typ_app (SailAST.Id xaa, [SailAST.A_bool nc]))
-> (if ((xaa : string) = "atom_bool") && ((xb : string) = "bool")
     then Predicate.single [nc] else Predicate.bot_pred)
                                      |
(SailAST.Typ_id (SailAST.Id _),
  SailAST.Typ_app (SailAST.Id _, SailAST.A_bool _ :: _ :: _))
-> Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_app (SailAST.Operator _, _)) ->
Predicate.bot_pred
                                      |
(SailAST.Typ_id (SailAST.Id _), SailAST.Typ_exist (_, _, _)) ->
Predicate.bot_pred
                                      | (SailAST.Typ_id (SailAST.Operator _), _)
-> Predicate.bot_pred
                                      | (SailAST.Typ_var _, _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_fn (_, _, _), _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_bidir (_, _, _), _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_tup _, _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_app (_, _), _) ->
Predicate.bot_pred
                                      | (SailAST.Typ_exist (_, _, _), _) ->
Predicate.bot_pred))))))))))))))))
and match_arg_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (SailAST.A_nexp _, _) -> Predicate.bot_pred
            | (SailAST.A_typ _, SailAST.A_nexp _) -> Predicate.bot_pred
            | (SailAST.A_typ t1, SailAST.A_typ t2) ->
              Predicate.bind (match_i_i_o t1 t2) Predicate.single
            | (SailAST.A_typ _, SailAST.A_order _) -> Predicate.bot_pred
            | (SailAST.A_typ _, SailAST.A_bool _) -> Predicate.bot_pred
            | (SailAST.A_order _, _) -> Predicate.bot_pred
            | (SailAST.A_bool _, _) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a
              with (SailAST.A_nexp ne1, SailAST.A_nexp ne2) ->
                Predicate.bind (match_nexp_i_i_o ne1 ne2) Predicate.single
              | (SailAST.A_nexp _, SailAST.A_typ _) -> Predicate.bot_pred
              | (SailAST.A_nexp _, SailAST.A_order _) -> Predicate.bot_pred
              | (SailAST.A_nexp _, SailAST.A_bool _) -> Predicate.bot_pred
              | (SailAST.A_typ _, _) -> Predicate.bot_pred
              | (SailAST.A_order _, _) -> Predicate.bot_pred
              | (SailAST.A_bool _, _) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a with (SailAST.A_nexp _, _) -> Predicate.bot_pred
                | (SailAST.A_typ _, _) -> Predicate.bot_pred
                | (SailAST.A_order _, _) -> Predicate.bot_pred
                | (SailAST.A_bool _, SailAST.A_nexp _) -> Predicate.bot_pred
                | (SailAST.A_bool _, SailAST.A_typ _) -> Predicate.bot_pred
                | (SailAST.A_bool _, SailAST.A_order _) -> Predicate.bot_pred
                | (SailAST.A_bool nc1, SailAST.A_bool nc2) ->
                  Predicate.bind (match_nc_i_i_o nc1 nc2) Predicate.single)))
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a with (SailAST.A_nexp _, _) -> Predicate.bot_pred
                | (SailAST.A_typ _, _) -> Predicate.bot_pred
                | (SailAST.A_order _, SailAST.A_nexp _) -> Predicate.bot_pred
                | (SailAST.A_order _, SailAST.A_typ _) -> Predicate.bot_pred
                | (SailAST.A_order ord, SailAST.A_order orda) ->
                  (if SailAST.equal_order ord orda then Predicate.single []
                    else Predicate.bot_pred)
                | (SailAST.A_order _, SailAST.A_bool _) -> Predicate.bot_pred
                | (SailAST.A_bool _, _) -> Predicate.bot_pred)))))
and match_arg_list_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], []) -> Predicate.single []
            | ([], _ :: _) -> Predicate.bot_pred
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (_ :: _, []) -> Predicate.bot_pred
            | (a1 :: as1, a2 :: as2) ->
              Predicate.bind (match_arg_list_i_i_o as1 as2)
                (fun xb ->
                  Predicate.bind (match_arg_i_i_o a1 a2)
                    (fun xaa -> Predicate.single (xaa @ xb))))))
and match_list_i_i_o
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], []) -> Predicate.single []
            | ([], _ :: _) -> Predicate.bot_pred
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (_ :: _, []) -> Predicate.bot_pred
            | (t1 :: ts1, t2 :: ts2) ->
              Predicate.bind (match_list_i_i_o ts1 ts2)
                (fun xb ->
                  Predicate.bind (match_i_i_o t1 t2)
                    (fun xaa -> Predicate.single (xaa @ xb))))));;

let rec subtype_i_i_i
  x xa xb =
    Predicate.bind (Predicate.single (x, (xa, xb)))
      (fun (env, (t1, t2)) ->
        Predicate.bind
          (Predicate.if_pred
            (trace
              ([Stringa.Chara
                  (false, false, true, false, true, true, true, false);
                 Stringa.Chara
                   (true, false, false, false, true, true, false, false);
                 Stringa.Chara
                   (true, false, true, true, true, true, false, false)] @
                ShowAST.shows_prec_typ Arith.Zero_nat t1 [])))
          (fun () ->
            Predicate.bind
              (Predicate.if_pred
                (trace
                  ([Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                     Stringa.Chara
                       (false, true, false, false, true, true, false, false);
                     Stringa.Chara
                       (true, false, true, true, true, true, false, false)] @
                    ShowAST.shows_prec_typ Arith.Zero_nat t2 [])))
              (fun () ->
                Predicate.bind (normalise_i_i_o env t1)
                  (fun a ->
                    (match a
                      with SailAST.Typ_internal_unknown -> Predicate.bot_pred
                      | SailAST.Typ_id _ -> Predicate.bot_pred
                      | SailAST.Typ_var _ -> Predicate.bot_pred
                      | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_bidir (_, _, _) -> Predicate.bot_pred
                      | SailAST.Typ_tup _ -> Predicate.bot_pred
                      | SailAST.Typ_app (_, _) -> Predicate.bot_pred
                      | SailAST.Typ_exist (_, _, t1a) ->
                        Predicate.bind (normalise_i_i_o env t2)
                          (fun aa ->
                            (match aa
                              with SailAST.Typ_internal_unknown ->
                                Predicate.bot_pred
                              | SailAST.Typ_id _ -> Predicate.bot_pred
                              | SailAST.Typ_var _ -> Predicate.bot_pred
                              | SailAST.Typ_fn (_, _, _) -> Predicate.bot_pred
                              | SailAST.Typ_bidir (_, _, _) ->
                                Predicate.bot_pred
                              | SailAST.Typ_tup _ -> Predicate.bot_pred
                              | SailAST.Typ_app (_, _) -> Predicate.bot_pred
                              | SailAST.Typ_exist (_, _, t2a) ->
                                Predicate.bind (match_i_i_o t1a t2a)
                                  (fun xc ->
                                    Predicate.bind
                                      (Predicate.if_pred
(trace
  ([Stringa.Chara (false, true, true, true, false, true, true, false);
     Stringa.Chara (true, true, false, false, false, true, true, false);
     Stringa.Chara (true, true, false, false, true, true, true, false);
     Stringa.Chara (true, false, true, true, true, true, false, false)] @
    Lista.maps (fun xd -> ShowAST.shows_prec_n_constraint Arith.Zero_nat xd [])
      xc)))
                                      (fun () ->
Predicate.bind (Predicate.if_pred (Env.prove env (nc_and_list xc)))
  (fun () -> Predicate.single ()))))))))));;

let rec check_pat_i_o
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a
               with SailAST.P_lit (tan, lit) ->
                 Predicate.bind (eq_o_i (Env.get tan))
                   (fun aa ->
                     (match aa with None -> Predicate.bot_pred
                       | Some (env, t) ->
                         Predicate.bind (check_lit_i_i_i env lit t)
                           (fun () -> Predicate.single [])))
               | SailAST.P_wild _ -> Predicate.bot_pred
               | SailAST.P_or (_, _, _) -> Predicate.bot_pred
               | SailAST.P_not (_, _) -> Predicate.bot_pred
               | SailAST.P_as (_, _, _) -> Predicate.bot_pred
               | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
               | SailAST.P_id (_, _) -> Predicate.bot_pred
               | SailAST.P_var (_, _, _) -> Predicate.bot_pred
               | SailAST.P_app (_, _, _) -> Predicate.bot_pred
               | SailAST.P_vector (_, _) -> Predicate.bot_pred
               | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
               | SailAST.P_tup (_, _) -> Predicate.bot_pred
               | SailAST.P_list (_, _) -> Predicate.bot_pred
               | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
               | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
         (Predicate.sup_pred
           (Predicate.bind (Predicate.single xa)
             (fun a ->
               (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
                 | SailAST.P_wild _ -> Predicate.single []
                 | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_not (_, _) -> Predicate.bot_pred
                 | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_id (_, _) -> Predicate.bot_pred
                 | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_vector (_, _) -> Predicate.bot_pred
                 | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
                 | SailAST.P_tup (_, _) -> Predicate.bot_pred
                 | SailAST.P_list (_, _) -> Predicate.bot_pred
                 | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                 | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
           (Predicate.sup_pred
             (Predicate.bind (Predicate.single xa)
               (fun a ->
                 (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
                   | SailAST.P_wild _ -> Predicate.bot_pred
                   | SailAST.P_or (_, p1, p2) ->
                     Predicate.bind (check_pat_i_o p1)
                       (fun x ->
                         Predicate.bind (check_pat_i_o p2)
                           (fun xaa -> Predicate.single (x @ xaa)))
                   | SailAST.P_not (_, _) -> Predicate.bot_pred
                   | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                   | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                   | SailAST.P_id (_, _) -> Predicate.bot_pred
                   | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                   | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                   | SailAST.P_vector (_, _) -> Predicate.bot_pred
                   | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
                   | SailAST.P_tup (_, _) -> Predicate.bot_pred
                   | SailAST.P_list (_, _) -> Predicate.bot_pred
                   | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                   | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
             (Predicate.sup_pred
               (Predicate.bind (Predicate.single xa)
                 (fun a ->
                   (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
                     | SailAST.P_wild _ -> Predicate.bot_pred
                     | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_not (_, p1) ->
                       Predicate.bind (check_pat_i_o p1) Predicate.single
                     | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_id (_, _) -> Predicate.bot_pred
                     | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_vector (_, _) -> Predicate.bot_pred
                     | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
                     | SailAST.P_tup (_, _) -> Predicate.bot_pred
                     | SailAST.P_list (_, _) -> Predicate.bot_pred
                     | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                     | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
               (Predicate.sup_pred
                 (Predicate.bind (Predicate.single xa)
                   (fun a ->
                     (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
                       | SailAST.P_wild _ -> Predicate.bot_pred
                       | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                       | SailAST.P_not (_, _) -> Predicate.bot_pred
                       | SailAST.P_as (_, pat, _) ->
                         Predicate.bind (check_pat_i_o pat) Predicate.single
                       | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                       | SailAST.P_id (_, _) -> Predicate.bot_pred
                       | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                       | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                       | SailAST.P_vector (_, _) -> Predicate.bot_pred
                       | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
                       | SailAST.P_tup (_, _) -> Predicate.bot_pred
                       | SailAST.P_list (_, _) -> Predicate.bot_pred
                       | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                       | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
                 (Predicate.sup_pred
                   (Predicate.bind (Predicate.single xa)
                     (fun a ->
                       (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
                         | SailAST.P_wild _ -> Predicate.bot_pred
                         | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                         | SailAST.P_not (_, _) -> Predicate.bot_pred
                         | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                         | SailAST.P_typ (_, _, pat) ->
                           Predicate.bind (check_pat_i_o pat) Predicate.single
                         | SailAST.P_id (_, _) -> Predicate.bot_pred
                         | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                         | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                         | SailAST.P_vector (_, _) -> Predicate.bot_pred
                         | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
                         | SailAST.P_tup (_, _) -> Predicate.bot_pred
                         | SailAST.P_list (_, _) -> Predicate.bot_pred
                         | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                         | SailAST.P_string_append (_, _) ->
                           Predicate.bot_pred)))
                   (Predicate.sup_pred
                     (Predicate.bind (Predicate.single xa)
                       (fun a ->
                         (match a
                           with SailAST.P_lit (_, _) -> Predicate.bot_pred
                           | SailAST.P_wild _ -> Predicate.bot_pred
                           | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_not (_, _) -> Predicate.bot_pred
                           | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_id (tan, x) ->
                             Predicate.bind
                               (eq_i_i (Option.equal_option SailAST.equal_typ)
                                 None (Env.lookup_enum tan x))
                               (fun () ->
                                 Predicate.bind (eq_o_i (Env.get tan))
                                   (fun aa ->
                                     (match aa with None -> Predicate.bot_pred
                                       | Some (_, t) ->
 Predicate.single [(x, (Env.Immutable, t))])))
                           | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_vector (_, _) -> Predicate.bot_pred
                           | SailAST.P_vector_concat (_, _) ->
                             Predicate.bot_pred
                           | SailAST.P_tup (_, _) -> Predicate.bot_pred
                           | SailAST.P_list (_, _) -> Predicate.bot_pred
                           | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                           | SailAST.P_string_append (_, _) ->
                             Predicate.bot_pred)))
                     (Predicate.sup_pred
                       (Predicate.bind (Predicate.single xa)
                         (fun a ->
                           (match a
                             with SailAST.P_lit (_, _) -> Predicate.bot_pred
                             | SailAST.P_wild _ -> Predicate.bot_pred
                             | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_not (_, _) -> Predicate.bot_pred
                             | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_id (tan, x) ->
                               Predicate.bind (eq_o_i (Env.get tan))
                                 (fun aa ->
                                   (match aa with None -> Predicate.bot_pred
                                     | Some (env, t1) ->
                                       Predicate.bind
 (eq_o_i (Env.lookup_enum tan x))
 (fun ab ->
   (match ab with None -> Predicate.bot_pred
     | Some t2 ->
       Predicate.bind (subtype_i_i_i env t2 t1)
         (fun () -> Predicate.single [])))))
                             | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_vector (_, _) -> Predicate.bot_pred
                             | SailAST.P_vector_concat (_, _) ->
                               Predicate.bot_pred
                             | SailAST.P_tup (_, _) -> Predicate.bot_pred
                             | SailAST.P_list (_, _) -> Predicate.bot_pred
                             | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                             | SailAST.P_string_append (_, _) ->
                               Predicate.bot_pred)))
                       (Predicate.sup_pred
                         (Predicate.bind (Predicate.single xa)
                           (fun a ->
                             (match a
                               with SailAST.P_lit (_, _) -> Predicate.bot_pred
                               | SailAST.P_wild _ -> Predicate.bot_pred
                               | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                               | SailAST.P_not (_, _) -> Predicate.bot_pred
                               | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                               | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                               | SailAST.P_id (_, _) -> Predicate.bot_pred
                               | SailAST.P_var (_, pat, _) ->
                                 Predicate.bind (check_pat_i_o pat)
                                   Predicate.single
                               | SailAST.P_app (_, _, _) -> Predicate.bot_pred
                               | SailAST.P_vector (_, _) -> Predicate.bot_pred
                               | SailAST.P_vector_concat (_, _) ->
                                 Predicate.bot_pred
                               | SailAST.P_tup (_, _) -> Predicate.bot_pred
                               | SailAST.P_list (_, _) -> Predicate.bot_pred
                               | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
                               | SailAST.P_string_append (_, _) ->
                                 Predicate.bot_pred)))
                         (Predicate.sup_pred
                           (Predicate.bind (Predicate.single xa)
                             (fun a ->
                               (match a
                                 with SailAST.P_lit (_, _) -> Predicate.bot_pred
                                 | SailAST.P_wild _ -> Predicate.bot_pred
                                 | SailAST.P_or (_, _, _) -> Predicate.bot_pred
                                 | SailAST.P_not (_, _) -> Predicate.bot_pred
                                 | SailAST.P_as (_, _, _) -> Predicate.bot_pred
                                 | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
                                 | SailAST.P_id (_, _) -> Predicate.bot_pred
                                 | SailAST.P_var (_, _, _) -> Predicate.bot_pred
                                 | SailAST.P_app (_, _, []) ->
                                   Predicate.bot_pred
                                 | SailAST.P_app (_, _, [parg]) ->
                                   Predicate.bind (check_pat_i_o parg)
                                     Predicate.single
                                 | SailAST.P_app (_, _, _ :: _ :: _) ->
                                   Predicate.bot_pred
                                 | SailAST.P_vector (_, _) -> Predicate.bot_pred
                                 | SailAST.P_vector_concat (_, _) ->
                                   Predicate.bot_pred
                                 | SailAST.P_tup (_, _) -> Predicate.bot_pred
                                 | SailAST.P_list (_, _) -> Predicate.bot_pred
                                 | SailAST.P_cons (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.P_string_append (_, _) ->
                                   Predicate.bot_pred)))
                           (Predicate.sup_pred
                             (Predicate.bind (Predicate.single xa)
                               (fun a ->
                                 (match a
                                   with SailAST.P_lit (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_wild _ -> Predicate.bot_pred
                                   | SailAST.P_or (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_not (_, _) -> Predicate.bot_pred
                                   | SailAST.P_as (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_typ (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_id (_, _) -> Predicate.bot_pred
                                   | SailAST.P_var (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_app (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_vector (_, pats) ->
                                     Predicate.bind (check_pat_list_i_o pats)
                                       Predicate.single
                                   | SailAST.P_vector_concat (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_tup (_, _) -> Predicate.bot_pred
                                   | SailAST.P_list (_, _) -> Predicate.bot_pred
                                   | SailAST.P_cons (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.P_string_append (_, _) ->
                                     Predicate.bot_pred)))
                             (Predicate.sup_pred
                               (Predicate.bind (Predicate.single xa)
                                 (fun a ->
                                   (match a
                                     with SailAST.P_lit (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_wild _ -> Predicate.bot_pred
                                     | SailAST.P_or (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_not (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_as (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_typ (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_id (_, _) -> Predicate.bot_pred
                                     | SailAST.P_var (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_app (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_vector (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_vector_concat (_, pats) ->
                                       Predicate.bind (check_pat_list_i_o pats)
 Predicate.single
                                     | SailAST.P_tup (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_list (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_cons (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.P_string_append (_, _) ->
                                       Predicate.bot_pred)))
                               (Predicate.sup_pred
                                 (Predicate.bind (Predicate.single xa)
                                   (fun a ->
                                     (match a
                                       with SailAST.P_lit (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_wild _ -> Predicate.bot_pred
                                       | SailAST.P_or (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_not (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_as (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_typ (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_id (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_var (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_app (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_vector (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_vector_concat (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_tup (_, pat_list) ->
 Predicate.bind (check_pat_list_i_o pat_list) Predicate.single
                                       | SailAST.P_list (_, _) ->
 Predicate.bot_pred
                                       | SailAST.P_cons (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.P_string_append (_, _) ->
 Predicate.bot_pred)))
                                 (Predicate.sup_pred
                                   (Predicate.bind (Predicate.single xa)
                                     (fun a ->
                                       (match a
 with SailAST.P_lit (_, _) -> Predicate.bot_pred
 | SailAST.P_wild _ -> Predicate.bot_pred
 | SailAST.P_or (_, _, _) -> Predicate.bot_pred
 | SailAST.P_not (_, _) -> Predicate.bot_pred
 | SailAST.P_as (_, _, _) -> Predicate.bot_pred
 | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
 | SailAST.P_id (_, _) -> Predicate.bot_pred
 | SailAST.P_var (_, _, _) -> Predicate.bot_pred
 | SailAST.P_app (_, _, _) -> Predicate.bot_pred
 | SailAST.P_vector (_, _) -> Predicate.bot_pred
 | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
 | SailAST.P_tup (_, _) -> Predicate.bot_pred
 | SailAST.P_list (_, pat_list) ->
   Predicate.bind (check_pat_list_i_o pat_list) Predicate.single
 | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
 | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
                                   (Predicate.sup_pred
                                     (Predicate.bind (Predicate.single xa)
                                       (fun a ->
 (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
   | SailAST.P_wild _ -> Predicate.bot_pred
   | SailAST.P_or (_, _, _) -> Predicate.bot_pred
   | SailAST.P_not (_, _) -> Predicate.bot_pred
   | SailAST.P_as (_, _, _) -> Predicate.bot_pred
   | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
   | SailAST.P_id (_, _) -> Predicate.bot_pred
   | SailAST.P_var (_, _, _) -> Predicate.bot_pred
   | SailAST.P_app (_, _, _) -> Predicate.bot_pred
   | SailAST.P_vector (_, _) -> Predicate.bot_pred
   | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
   | SailAST.P_tup (_, _) -> Predicate.bot_pred
   | SailAST.P_list (_, _) -> Predicate.bot_pred
   | SailAST.P_cons (_, p1, p2) ->
     Predicate.bind (check_pat_i_o p1)
       (fun x ->
         Predicate.bind (check_pat_i_o p2)
           (fun xaa -> Predicate.single (x @ xaa)))
   | SailAST.P_string_append (_, _) -> Predicate.bot_pred)))
                                     (Predicate.bind (Predicate.single xa)
                                       (fun a ->
 (match a with SailAST.P_lit (_, _) -> Predicate.bot_pred
   | SailAST.P_wild _ -> Predicate.bot_pred
   | SailAST.P_or (_, _, _) -> Predicate.bot_pred
   | SailAST.P_not (_, _) -> Predicate.bot_pred
   | SailAST.P_as (_, _, _) -> Predicate.bot_pred
   | SailAST.P_typ (_, _, _) -> Predicate.bot_pred
   | SailAST.P_id (_, _) -> Predicate.bot_pred
   | SailAST.P_var (_, _, _) -> Predicate.bot_pred
   | SailAST.P_app (_, _, _) -> Predicate.bot_pred
   | SailAST.P_vector (_, _) -> Predicate.bot_pred
   | SailAST.P_vector_concat (_, _) -> Predicate.bot_pred
   | SailAST.P_tup (_, _) -> Predicate.bot_pred
   | SailAST.P_list (_, _) -> Predicate.bot_pred
   | SailAST.P_cons (_, _, _) -> Predicate.bot_pred
   | SailAST.P_string_append (_, pat_list) ->
     Predicate.bind (check_pat_list_i_o pat_list)
       Predicate.single)))))))))))))))))
and check_pat_list_i_o
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with [] -> Predicate.single []
               | _ :: _ -> Predicate.bot_pred)))
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with [] -> Predicate.bot_pred
               | pat :: pats ->
                 Predicate.bind (check_pat_list_i_o pats)
                   (fun x ->
                     Predicate.bind (check_pat_i_o pat)
                       (fun xaa -> Predicate.single (xaa @ x))))));;

let rec subenv_i_i
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun (_, _) -> Predicate.single ());;

let rec locals_in
  uu x1 = match uu, x1 with uu, [] -> true
    | env, (x, (mut, typ)) :: gs ->
        (match Env.lookup_local_id_env env x with None -> false
          | Some _ -> locals_in env gs);;

let rec check_local_binds_i_i
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.single ()
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (exp :: exps, bindings) ->
              Predicate.bind (check_local_binds_i_i exps bindings)
                (fun () ->
                  Predicate.bind (eq_o_i (Env.get_env_exp exp))
                    (fun aa ->
                      (match aa with None -> Predicate.bot_pred
                        | Some env ->
                          Predicate.bind
                            (Predicate.if_pred (locals_in env bindings))
                            (fun () -> Predicate.single ())))))));;

let rec subtype_exp_i_i
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun (exp, typ2) ->
        Predicate.bind (eq_o_i (Env.get_env_exp exp))
          (fun a ->
            (match a with None -> Predicate.bot_pred
              | Some env ->
                Predicate.bind (eq_o_i (Env.type_of_exp exp))
                  (fun aa ->
                    (match aa with None -> Predicate.bot_pred
                      | Some typ1 ->
                        Predicate.bind (subtype_i_i_i env typ1 typ2)
                          (fun () -> Predicate.single ()))))));;

let rec subtype_tan_i_i
  x xa =
    Predicate.bind (Predicate.single (x, xa))
      (fun (t, tan) ->
        Predicate.bind (eq_o_i (Env.get_env tan))
          (fun a ->
            (match a with None -> Predicate.bot_pred
              | Some env ->
                Predicate.bind (eq_o_i (Env.get_type tan))
                  (fun aa ->
                    (match aa with None -> Predicate.bot_pred
                      | Some ta ->
                        Predicate.bind (subtype_i_i_i env t ta)
                          (fun () -> Predicate.single ()))))));;

let rec check_lexp_vector_list_i_i_i
  x xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, (xa, xb)))
        (fun a ->
          (match a with ([], (_, _)) -> Predicate.single ()
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, (xa, xb)))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (lexp :: lexps, (order, typ)) ->
              Predicate.bind (check_lexp_vector_list_i_i_i lexps order typ)
                (fun () ->
                  Predicate.bind (eq_o_i (Env.type_of_lexp lexp))
                    (fun aa ->
                      (match aa with None -> Predicate.bot_pred
                        | Some t ->
                          Predicate.bind
                            (eq_o_i (Env.deconstruct_vector_type t))
                            (fun ab ->
                              (match ab with None -> Predicate.bot_pred
                                | Some (_, (ordera, typa)) ->
                                  (if SailAST.equal_order order ordera &&
SailAST.equal_typa typ typa
                                    then Predicate.single ()
                                    else Predicate.bot_pred)))))))));;

let rec add_locals env uu = env;;

let rec check_letbind_i_o
  xa = Predicate.bind (Predicate.single xa)
         (fun (SailAST.LB_val (_, pat, exp)) ->
           Predicate.bind (check_pat_i_o pat)
             (fun x ->
               Predicate.bind (check_exp_i_o exp)
                 (fun _ -> Predicate.single x)))
and check_exp_i_o
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
               | SailAST.E_id (_, _) -> Predicate.bot_pred
               | SailAST.E_lit (tan, lit) ->
                 Predicate.bind (eq_o_i (Env.get tan))
                   (fun aa ->
                     (match aa with None -> Predicate.bot_pred
                       | Some (env, t) ->
                         Predicate.bind (check_lit_i_i_i env lit t)
                           (fun () -> Predicate.single [])))
               | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
               | SailAST.E_app (_, _, _) -> Predicate.bot_pred
               | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_tuple (_, _) -> Predicate.bot_pred
               | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
               | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector (_, _) -> Predicate.bot_pred
               | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                 Predicate.bot_pred
               | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
               | SailAST.E_list (_, _) -> Predicate.bot_pred
               | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
               | SailAST.E_record (_, _) -> Predicate.bot_pred
               | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
               | SailAST.E_field (_, _, _) -> Predicate.bot_pred
               | SailAST.E_case (_, _, _) -> Predicate.bot_pred
               | SailAST.E_let (_, _, _) -> Predicate.bot_pred
               | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
               | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
               | SailAST.E_return (_, _) -> Predicate.bot_pred
               | SailAST.E_exit (_, _) -> Predicate.bot_pred
               | SailAST.E_ref (_, _) -> Predicate.bot_pred
               | SailAST.E_throw (_, _) -> Predicate.bot_pred
               | SailAST.E_try (_, _, _) -> Predicate.bot_pred
               | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
               | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
               | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
               | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
         (Predicate.sup_pred
           (Predicate.bind (Predicate.single xa)
             (fun a ->
               (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                 | SailAST.E_id (tan, x) ->
                   Predicate.bind
                     (Predicate.if_pred
                       (trace
                         [Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                           Stringa.Chara
                             (false, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (true, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, false, true,
                               false)]))
                     (fun () ->
                       Predicate.bind (eq_o_i (Env.get tan))
                         (fun aa ->
                           (match aa with None -> Predicate.bot_pred
                             | Some (env, t2) ->
                               Predicate.bind (eq_o_i (Env.lookup_id tan x))
                                 (fun ab ->
                                   (match ab with None -> Predicate.bot_pred
                                     | Some t1 ->
                                       Predicate.bind (subtype_i_i_i env t1 t2)
 (fun () -> Predicate.single []))))))
                 | SailAST.E_lit (_, _) -> Predicate.bot_pred
                 | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                 | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector (_, _) -> Predicate.bot_pred
                 | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                   Predicate.bot_pred
                 | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_list (_, _) -> Predicate.bot_pred
                 | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_record (_, _) -> Predicate.bot_pred
                 | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                 | SailAST.E_return (_, _) -> Predicate.bot_pred
                 | SailAST.E_exit (_, _) -> Predicate.bot_pred
                 | SailAST.E_ref (_, _) -> Predicate.bot_pred
                 | SailAST.E_throw (_, _) -> Predicate.bot_pred
                 | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                 | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                 | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
           (Predicate.sup_pred
             (Predicate.bind (Predicate.single xa)
               (fun a ->
                 (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                   | SailAST.E_id (_, _) -> Predicate.bot_pred
                   | SailAST.E_lit (_, _) -> Predicate.bot_pred
                   | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_tuple (tan, exps) ->
                     Predicate.bind (eq_o_i (Env.get tan))
                       (fun aa ->
                         (match aa with None -> Predicate.bot_pred
                           | Some (_, t) ->
                             Predicate.bind (eq_o_i t)
                               (fun ab ->
                                 (match ab
                                   with SailAST.Typ_internal_unknown ->
                                     Predicate.bot_pred
                                   | SailAST.Typ_id _ -> Predicate.bot_pred
                                   | SailAST.Typ_var _ -> Predicate.bot_pred
                                   | SailAST.Typ_fn (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.Typ_bidir (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.Typ_tup typs ->
                                     Predicate.bind
                                       (check_exp_list_i_i exps typs)
                                       (fun () -> Predicate.single [])
                                   | SailAST.Typ_app (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.Typ_exist (_, _, _) ->
                                     Predicate.bot_pred))))
                   | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_vector (_, _) -> Predicate.bot_pred
                   | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_vector_subrange (_, _, _, _) ->
                     Predicate.bot_pred
                   | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                     Predicate.bot_pred
                   | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_list (_, _) -> Predicate.bot_pred
                   | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_record (_, _) -> Predicate.bot_pred
                   | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                   | SailAST.E_return (_, _) -> Predicate.bot_pred
                   | SailAST.E_exit (_, _) -> Predicate.bot_pred
                   | SailAST.E_ref (_, _) -> Predicate.bot_pred
                   | SailAST.E_throw (_, _) -> Predicate.bot_pred
                   | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                   | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                   | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
             (Predicate.sup_pred
               (Predicate.bind (Predicate.single xa)
                 (fun a ->
                   (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                     | SailAST.E_id (_, _) -> Predicate.bot_pred
                     | SailAST.E_lit (_, _) -> Predicate.bot_pred
                     | SailAST.E_cast (_, t, exp) ->
                       Predicate.bind (subtype_exp_i_i exp t)
                         (fun () ->
                           Predicate.bind (check_exp_i_o exp) Predicate.single)
                     | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                     | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_vector (_, _) -> Predicate.bot_pred
                     | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_vector_subrange (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_update (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_list (_, _) -> Predicate.bot_pred
                     | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_record (_, _) -> Predicate.bot_pred
                     | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                     | SailAST.E_return (_, _) -> Predicate.bot_pred
                     | SailAST.E_exit (_, _) -> Predicate.bot_pred
                     | SailAST.E_ref (_, _) -> Predicate.bot_pred
                     | SailAST.E_throw (_, _) -> Predicate.bot_pred
                     | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_internal_plet (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                     | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                     | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
               (Predicate.sup_pred
                 (Predicate.bind (Predicate.single xa)
                   (fun a ->
                     (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                       | SailAST.E_id (_, _) -> Predicate.bot_pred
                       | SailAST.E_lit (_, _) -> Predicate.bot_pred
                       | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_app (tan, fid, exps) ->
                         Predicate.bind
                           (Predicate.if_pred
                             (trace
                               ([Stringa.Chara
                                   (true, false, true, false, false, false,
                                     true, false);
                                  Stringa.Chara
                                    (true, true, true, true, true, false, true,
                                      false);
                                  Stringa.Chara
                                    (true, false, false, false, false, true,
                                      true, false);
                                  Stringa.Chara
                                    (false, false, false, false, true, true,
                                      true, false);
                                  Stringa.Chara
                                    (false, false, false, false, true, true,
                                      true, false);
                                  Stringa.Chara
                                    (false, false, false, false, false, true,
                                      false, false)] @
                                 ShowAST.show_tannot tan)))
                           (fun () ->
                             Predicate.bind
                               (Predicate.if_pred
                                 (trace
                                   [Stringa.Chara
                                      (true, false, true, false, false, false,
true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (true, false, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, false, true,
 false, false);
                                     Stringa.Chara
                                       (true, false, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, false, true,
 false, false);
                                     Stringa.Chara
                                       (true, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (true, false, false, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, false, true,
 false, false);
                                     Stringa.Chara
                                       (true, false, false, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, false, true,
 false, false);
                                     Stringa.Chara
                                       (true, false, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, true, true,
 true, false)]))
                               (fun () ->
                                 Predicate.bind
                                   (Predicate.if_pred
                                     (trace
                                       [Stringa.Chara
  (true, false, true, false, false, false, true, false);
 Stringa.Chara (true, true, true, true, true, false, true, false);
 Stringa.Chara (true, false, false, false, false, true, true, false);
 Stringa.Chara (false, false, false, false, true, true, true, false);
 Stringa.Chara (false, false, false, false, true, true, true, false);
 Stringa.Chara (false, false, false, false, false, true, false, false);
 Stringa.Chara (true, false, false, false, false, true, true, false);
 Stringa.Chara (false, true, true, false, false, true, true, false);
 Stringa.Chara (false, false, true, false, true, true, true, false);
 Stringa.Chara (true, false, true, false, false, true, true, false);
 Stringa.Chara (false, true, false, false, true, true, true, false);
 Stringa.Chara (false, false, false, false, false, true, false, false);
 Stringa.Chara (true, true, false, false, true, true, true, false);
 Stringa.Chara (true, false, true, false, true, true, true, false);
 Stringa.Chara (false, true, false, false, false, true, true, false);
 Stringa.Chara (true, true, false, false, true, true, true, false);
 Stringa.Chara (false, false, true, false, true, true, true, false);
 Stringa.Chara (true, true, true, true, true, false, true, false);
 Stringa.Chara (true, false, false, true, false, true, true, false);
 Stringa.Chara (false, true, true, true, false, true, true, false);
 Stringa.Chara (true, true, false, false, true, true, true, false);
 Stringa.Chara (false, false, true, false, true, true, true, false);
 Stringa.Chara (false, false, false, false, false, true, false, false);
 Stringa.Chara (false, true, false, false, true, true, true, false);
 Stringa.Chara (true, false, true, false, false, true, true, false);
 Stringa.Chara (false, false, true, false, true, true, true, false)]))
                                   (fun () ->
                                     Predicate.bind (eq_o_i (Env.get tan))
                                       (fun aa ->
 (match aa with None -> Predicate.bot_pred
   | Some (_, t) ->
     Predicate.bind (eq_o_i (Env.lookup_fun tan fid))
       (fun ab ->
         (match ab with None -> Predicate.bot_pred
           | Some (in_typs, rett_typ) ->
             Predicate.bind (eq_o_i (Env.subst_inst_list tan in_typs))
               (fun ac ->
                 (match ac with None -> Predicate.bot_pred
                   | Some in_typs2 ->
                     Predicate.bind (check_exp_list_i_i exps in_typs2)
                       (fun () ->
                         Predicate.bind (eq_o_i (Env.subst_inst tan rett_typ))
                           (fun ad ->
                             (match ad with None -> Predicate.bot_pred
                               | Some ret_typ2 ->
                                 Predicate.bind
                                   (Predicate.if_pred
                                     (trace
                                       ([Stringa.Chara
   (true, false, true, false, false, false, true, false);
  Stringa.Chara (true, true, true, true, true, false, true, false);
  Stringa.Chara (true, false, false, false, false, true, true, false);
  Stringa.Chara (false, false, false, false, true, true, true, false);
  Stringa.Chara (false, false, false, false, true, true, true, false);
  Stringa.Chara (false, false, false, false, false, true, false, false);
  Stringa.Chara (true, true, false, false, true, true, true, false);
  Stringa.Chara (true, false, true, false, true, true, true, false);
  Stringa.Chara (false, true, false, false, false, true, true, false);
  Stringa.Chara (false, false, true, false, true, true, true, false);
  Stringa.Chara (true, false, false, true, true, true, true, false);
  Stringa.Chara (false, false, false, false, true, true, true, false);
  Stringa.Chara (true, false, true, false, false, true, true, false)] @
 [Stringa.Chara (false, false, true, false, true, true, true, false);
   Stringa.Chara (true, false, false, false, true, true, false, false);
   Stringa.Chara (true, false, true, true, true, true, false, false)] @
   ShowAST.shows_prec_typ Arith.Zero_nat ret_typ2 [] @
     [Stringa.Chara (false, false, true, false, true, true, true, false);
       Stringa.Chara (false, true, false, false, true, true, false, false);
       Stringa.Chara (true, false, true, true, true, true, false, false)] @
       ShowAST.shows_prec_typ Arith.Zero_nat t [])))
                                   (fun () ->
                                     Predicate.bind
                                       (subtype_tan_i_i ret_typ2 tan)
                                       (fun () ->
 Predicate.single []))))))))))))))
                       | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                       | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_for (_, _, _, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector (_, _) -> Predicate.bot_pred
                       | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_vector_subrange (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_list (_, _) -> Predicate.bot_pred
                       | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_record (_, _) -> Predicate.bot_pred
                       | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                       | SailAST.E_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_exit (_, _) -> Predicate.bot_pred
                       | SailAST.E_ref (_, _) -> Predicate.bot_pred
                       | SailAST.E_throw (_, _) -> Predicate.bot_pred
                       | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_internal_plet (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                       | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                 (Predicate.sup_pred
                   (Predicate.bind (Predicate.single xa)
                     (fun a ->
                       (match a
                         with SailAST.E_block (_, _) -> Predicate.bot_pred
                         | SailAST.E_id (_, _) -> Predicate.bot_pred
                         | SailAST.E_lit (_, _) -> Predicate.bot_pred
                         | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_app_infix (_, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                         | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                         | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                         | SailAST.E_for (_, _, _, _, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_vector (_, _) -> Predicate.bot_pred
                         | SailAST.E_vector_access (_, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_vector_subrange (_, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_vector_update (_, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_vector_append (_, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_list (_, _) -> Predicate.bot_pred
                         | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_record (tan, fexp_list) ->
                           Predicate.bind (eq_o_i (Env.get tan))
                             (fun aa ->
                               (match aa with None -> Predicate.bot_pred
                                 | Some (_, typ) ->
                                   Predicate.bind
                                     (check_fexp_list_i_i fexp_list typ)
                                     (fun () -> Predicate.single [])))
                         | SailAST.E_record_update (_, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                         | SailAST.E_return (_, _) -> Predicate.bot_pred
                         | SailAST.E_exit (_, _) -> Predicate.bot_pred
                         | SailAST.E_ref (_, _) -> Predicate.bot_pred
                         | SailAST.E_throw (_, _) -> Predicate.bot_pred
                         | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                         | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                         | SailAST.E_internal_plet (_, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.E_internal_return (_, _) ->
                           Predicate.bot_pred
                         | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                         | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                   (Predicate.sup_pred
                     (Predicate.bind (Predicate.single xa)
                       (fun a ->
                         (match a
                           with SailAST.E_block (_, _) -> Predicate.bot_pred
                           | SailAST.E_id (_, _) -> Predicate.bot_pred
                           | SailAST.E_lit (_, _) -> Predicate.bot_pred
                           | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_app_infix (_, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                           | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                           | SailAST.E_loop (_, _, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_for (_, _, _, _, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_vector (_, _) -> Predicate.bot_pred
                           | SailAST.E_vector_access (_, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_vector_subrange (_, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_vector_update (_, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_vector_append (_, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_list (_, _) -> Predicate.bot_pred
                           | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_record (_, _) -> Predicate.bot_pred
                           | SailAST.E_record_update (tan, exp, fexp_list) ->
                             Predicate.bind (check_exp_i_o exp)
                               (fun _ ->
                                 Predicate.bind (eq_o_i (Env.get tan))
                                   (fun aa ->
                                     (match aa with None -> Predicate.bot_pred
                                       | Some (_, typ) ->
 Predicate.bind (check_fexp_list_i_i fexp_list typ)
   (fun () -> Predicate.single []))))
                           | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                           | SailAST.E_return (_, _) -> Predicate.bot_pred
                           | SailAST.E_exit (_, _) -> Predicate.bot_pred
                           | SailAST.E_ref (_, _) -> Predicate.bot_pred
                           | SailAST.E_throw (_, _) -> Predicate.bot_pred
                           | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                           | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                           | SailAST.E_internal_plet (_, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.E_internal_return (_, _) ->
                             Predicate.bot_pred
                           | SailAST.E_internal_value (_, _) ->
                             Predicate.bot_pred
                           | SailAST.E_constraint (_, _) ->
                             Predicate.bot_pred)))
                     (Predicate.sup_pred
                       (Predicate.bind (Predicate.single xa)
                         (fun a ->
                           (match a
                             with SailAST.E_block (_, _) -> Predicate.bot_pred
                             | SailAST.E_id (_, _) -> Predicate.bot_pred
                             | SailAST.E_lit (_, _) -> Predicate.bot_pred
                             | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_app_infix (_, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                             | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                             | SailAST.E_loop (_, _, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_for (_, _, _, _, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_vector (_, _) -> Predicate.bot_pred
                             | SailAST.E_vector_access (_, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_vector_subrange (_, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_vector_update (_, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_vector_update_subrange (_, _, _, _, _)
                               -> Predicate.bot_pred
                             | SailAST.E_vector_append (_, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_list (_, _) -> Predicate.bot_pred
                             | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_record (_, _) -> Predicate.bot_pred
                             | SailAST.E_record_update (_, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_field (tan, exp, fid) ->
                               Predicate.bind (check_exp_i_o exp)
                                 (fun _ ->
                                   Predicate.bind (eq_o_i (Env.get tan))
                                     (fun aa ->
                                       (match aa with None -> Predicate.bot_pred
 | Some (env, t1) ->
   Predicate.bind (eq_o_i (Env.type_of_exp exp))
     (fun ab ->
       (match ab with None -> Predicate.bot_pred
         | Some rtype ->
           Predicate.bind (eq_o_i (Env.deconstruct_record_type rtype))
             (fun ac ->
               (match ac with None -> Predicate.bot_pred
                 | Some recid ->
                   Predicate.bind
                     (eq_o_i (Env.lookup_record_field_env env recid fid))
                     (fun ad ->
                       (match ad with None -> Predicate.bot_pred
                         | Some t2 ->
                           Predicate.bind (subtype_i_i_i env t1 t2)
                             (fun () -> Predicate.single []))))))))))
                             | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                             | SailAST.E_return (_, _) -> Predicate.bot_pred
                             | SailAST.E_exit (_, _) -> Predicate.bot_pred
                             | SailAST.E_ref (_, _) -> Predicate.bot_pred
                             | SailAST.E_throw (_, _) -> Predicate.bot_pred
                             | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                             | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                             | SailAST.E_internal_plet (_, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.E_internal_return (_, _) ->
                               Predicate.bot_pred
                             | SailAST.E_internal_value (_, _) ->
                               Predicate.bot_pred
                             | SailAST.E_constraint (_, _) ->
                               Predicate.bot_pred)))
                       (Predicate.sup_pred
                         (Predicate.bind (Predicate.single xa)
                           (fun a ->
                             (match a
                               with SailAST.E_block (_, _) -> Predicate.bot_pred
                               | SailAST.E_id (_, _) -> Predicate.bot_pred
                               | SailAST.E_lit (_, _) -> Predicate.bot_pred
                               | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_app_infix (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                               | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                               | SailAST.E_loop (_, _, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_for (_, _, _, _, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_vector (_, _) -> Predicate.bot_pred
                               | SailAST.E_vector_access (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_vector_subrange (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_vector_update (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_vector_update_subrange
                                   (_, _, _, _, _)
                                 -> Predicate.bot_pred
                               | SailAST.E_vector_append (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_list (_, _) -> Predicate.bot_pred
                               | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_record (_, _) -> Predicate.bot_pred
                               | SailAST.E_record_update (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_assign (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                               | SailAST.E_return (tan, exp) ->
                                 Predicate.bind (eq_o_i (Env.ret_type tan))
                                   (fun aa ->
                                     (match aa with None -> Predicate.bot_pred
                                       | Some r_typ ->
 Predicate.bind (check_exp_typ_i_i exp r_typ) (fun () -> Predicate.single [])))
                               | SailAST.E_exit (_, _) -> Predicate.bot_pred
                               | SailAST.E_ref (_, _) -> Predicate.bot_pred
                               | SailAST.E_throw (_, _) -> Predicate.bot_pred
                               | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                               | SailAST.E_assert (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_var (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_internal_plet (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_internal_return (_, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_internal_value (_, _) ->
                                 Predicate.bot_pred
                               | SailAST.E_constraint (_, _) ->
                                 Predicate.bot_pred)))
                         (Predicate.sup_pred
                           (Predicate.bind (Predicate.single xa)
                             (fun a ->
                               (match a
                                 with SailAST.E_block (_, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_id (_, _) -> Predicate.bot_pred
                                 | SailAST.E_lit (_, _) -> Predicate.bot_pred
                                 | SailAST.E_cast (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                                 | SailAST.E_app_infix (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                                 | SailAST.E_if (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_loop (_, _, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_for (_, _, _, _, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_vector (_, _) -> Predicate.bot_pred
                                 | SailAST.E_vector_access (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_vector_subrange (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_vector_update (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_vector_update_subrange
                                     (_, _, _, _, _)
                                   -> Predicate.bot_pred
                                 | SailAST.E_vector_append (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_list (_, _) -> Predicate.bot_pred
                                 | SailAST.E_cons (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_record (_, _) -> Predicate.bot_pred
                                 | SailAST.E_record_update (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_field (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_case (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                                 | SailAST.E_assign (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                                 | SailAST.E_return (_, _) -> Predicate.bot_pred
                                 | SailAST.E_exit (_, exp) ->
                                   Predicate.bind
                                     (check_exp_typ_i_i exp AstUtils.unit_typ)
                                     (fun () -> Predicate.single [])
                                 | SailAST.E_ref (_, _) -> Predicate.bot_pred
                                 | SailAST.E_throw (_, _) -> Predicate.bot_pred
                                 | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                                 | SailAST.E_assert (_, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_var (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_internal_plet (_, _, _, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_internal_return (_, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_internal_value (_, _) ->
                                   Predicate.bot_pred
                                 | SailAST.E_constraint (_, _) ->
                                   Predicate.bot_pred)))
                           (Predicate.sup_pred
                             (Predicate.bind (Predicate.single xa)
                               (fun a ->
                                 (match a
                                   with SailAST.E_block (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_id (_, _) -> Predicate.bot_pred
                                   | SailAST.E_lit (_, _) -> Predicate.bot_pred
                                   | SailAST.E_cast (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_app (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_app_infix (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_tuple (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_if (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_loop (_, _, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_for (_, _, _, _, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_vector (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_vector_access (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_vector_subrange (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_vector_update (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_vector_update_subrange
                                       (_, _, _, _, _)
                                     -> Predicate.bot_pred
                                   | SailAST.E_vector_append (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_list (_, _) -> Predicate.bot_pred
                                   | SailAST.E_cons (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_record (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_record_update (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_field (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_case (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_let (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_assign (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_sizeof (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_return (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_exit (_, _) -> Predicate.bot_pred
                                   | SailAST.E_ref (_, _) -> Predicate.bot_pred
                                   | SailAST.E_throw (_, exp) ->
                                     Predicate.bind
                                       (check_exp_typ_i_i exp
 (SailAST.Typ_id (SailAST.Id "exception")))
                                       (fun () -> Predicate.single [])
                                   | SailAST.E_try (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_assert (_, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_var (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_internal_plet (_, _, _, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_internal_return (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_internal_value (_, _) ->
                                     Predicate.bot_pred
                                   | SailAST.E_constraint (_, _) ->
                                     Predicate.bot_pred)))
                             (Predicate.sup_pred
                               (Predicate.bind (Predicate.single xa)
                                 (fun a ->
                                   (match a
                                     with SailAST.E_block (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_id (_, _) -> Predicate.bot_pred
                                     | SailAST.E_lit (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_cast (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_app (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_app_infix (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_tuple (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_if (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_loop (_, _, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_for (_, _, _, _, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_vector (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_vector_access (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_vector_subrange (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_vector_update (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_vector_update_subrange
 (_, _, _, _, _)
                                       -> Predicate.bot_pred
                                     | SailAST.E_vector_append (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_list (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_cons (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_record (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_record_update (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_field (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_case (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_let (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_assign (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_sizeof (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_return (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_exit (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_ref (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_throw (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_try (_, exp, pexps) ->
                                       Predicate.bind (check_pexps_i pexps)
 (fun () -> Predicate.bind (check_exp_i_o exp) (fun _ -> Predicate.single []))
                                     | SailAST.E_assert (_, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_var (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_internal_plet (_, _, _, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_internal_return (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_internal_value (_, _) ->
                                       Predicate.bot_pred
                                     | SailAST.E_constraint (_, _) ->
                                       Predicate.bot_pred)))
                               (Predicate.sup_pred
                                 (Predicate.bind (Predicate.single xa)
                                   (fun a ->
                                     (match a
                                       with SailAST.E_block (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_id (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_lit (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_cast (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_app (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_app_infix (_, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_tuple (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_if (_, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_loop (_, _, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_for (_, _, _, _, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_vector (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_vector_access (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_vector_subrange (_, _, _, _)
 -> Predicate.bot_pred
                                       | SailAST.E_vector_update (_, _, _, _) ->
 Predicate.bot_pred
                                       |
 SailAST.E_vector_update_subrange (_, _, _, _, _) -> Predicate.bot_pred
                                       | SailAST.E_vector_append (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_list (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_cons (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_record (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_record_update (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_field (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_case (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_let (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_assign (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_sizeof (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_return (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_exit (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_ref (tan, x) ->
 Predicate.bind (eq_o_i (Env.lookup_register tan x))
   (fun aa ->
     (match aa with None -> Predicate.bot_pred
       | Some t1 ->
         Predicate.bind (subtype_tan_i_i t1 tan)
           (fun () -> Predicate.single [])))
                                       | SailAST.E_throw (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_try (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_assert (_, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_var (_, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_internal_plet (_, _, _, _) ->
 Predicate.bot_pred
                                       | SailAST.E_internal_return (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_internal_value (_, _) ->
 Predicate.bot_pred
                                       | SailAST.E_constraint (_, _) ->
 Predicate.bot_pred)))
                                 (Predicate.sup_pred
                                   (Predicate.bind (Predicate.single xa)
                                     (fun a ->
                                       (match a
 with SailAST.E_block (_, _) -> Predicate.bot_pred
 | SailAST.E_id (_, _) -> Predicate.bot_pred
 | SailAST.E_lit (_, _) -> Predicate.bot_pred
 | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
 | SailAST.E_app (_, _, _) -> Predicate.bot_pred
 | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_tuple (_, _) -> Predicate.bot_pred
 | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
 | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
 | SailAST.E_vector (tan, exps) ->
   Predicate.bind (eq_o_i (Env.get tan))
     (fun aa ->
       (match aa with None -> Predicate.bot_pred
         | Some (env, _) ->
           Predicate.bind (eq_o_i (Env.is_vector_type tan))
             (fun ab ->
               (match ab with None -> Predicate.bot_pred
                 | Some (len, (_, typ)) ->
                   Predicate.bind
                     (check_exp_list_i_i exps
                       (Lista.replicate (Lista.size_list exps) typ))
                     (fun () ->
                       Predicate.bind
                         (Predicate.if_pred
                           (Env.prove env
                             (SailAST.NC_equal
                               (SailAST.Nexp_constant
                                  (integer_of_int2
                                    (Arith.of_nat Arith.semiring_1_int
                                      (Lista.size_list exps))),
                                 len))))
                         (fun () -> Predicate.single []))))))
 | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
 | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_vector_update_subrange (_, _, _, _, _) -> Predicate.bot_pred
 | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
 | SailAST.E_list (_, _) -> Predicate.bot_pred
 | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
 | SailAST.E_record (_, _) -> Predicate.bot_pred
 | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
 | SailAST.E_field (_, _, _) -> Predicate.bot_pred
 | SailAST.E_case (_, _, _) -> Predicate.bot_pred
 | SailAST.E_let (_, _, _) -> Predicate.bot_pred
 | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
 | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
 | SailAST.E_return (_, _) -> Predicate.bot_pred
 | SailAST.E_exit (_, _) -> Predicate.bot_pred
 | SailAST.E_ref (_, _) -> Predicate.bot_pred
 | SailAST.E_throw (_, _) -> Predicate.bot_pred
 | SailAST.E_try (_, _, _) -> Predicate.bot_pred
 | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
 | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
 | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
 | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
 | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                                   (Predicate.sup_pred
                                     (Predicate.bind (Predicate.single xa)
                                       (fun a ->
 (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
   | SailAST.E_id (_, _) -> Predicate.bot_pred
   | SailAST.E_lit (_, _) -> Predicate.bot_pred
   | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
   | SailAST.E_app (_, _, _) -> Predicate.bot_pred
   | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_tuple (_, _) -> Predicate.bot_pred
   | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
   | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
   | SailAST.E_vector (_, _) -> Predicate.bot_pred
   | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
   | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_vector_update_subrange (_, _, _, _, _) -> Predicate.bot_pred
   | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
   | SailAST.E_list (tan, exps) ->
     Predicate.bind (eq_o_i (Env.is_list_type tan))
       (fun aa ->
         (match aa with None -> Predicate.bot_pred
           | Some elem_typ ->
             Predicate.bind
               (check_exp_list_i_i exps
                 (Lista.replicate (Lista.size_list exps) elem_typ))
               (fun () -> Predicate.single [])))
   | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
   | SailAST.E_record (_, _) -> Predicate.bot_pred
   | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
   | SailAST.E_field (_, _, _) -> Predicate.bot_pred
   | SailAST.E_case (_, _, _) -> Predicate.bot_pred
   | SailAST.E_let (_, _, _) -> Predicate.bot_pred
   | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
   | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
   | SailAST.E_return (_, _) -> Predicate.bot_pred
   | SailAST.E_exit (_, _) -> Predicate.bot_pred
   | SailAST.E_ref (_, _) -> Predicate.bot_pred
   | SailAST.E_throw (_, _) -> Predicate.bot_pred
   | SailAST.E_try (_, _, _) -> Predicate.bot_pred
   | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
   | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
   | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
   | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
   | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                                     (Predicate.sup_pred
                                       (Predicate.bind (Predicate.single xa)
 (fun a ->
   (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
     | SailAST.E_id (_, _) -> Predicate.bot_pred
     | SailAST.E_lit (_, _) -> Predicate.bot_pred
     | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
     | SailAST.E_app (_, _, _) -> Predicate.bot_pred
     | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_tuple (_, _) -> Predicate.bot_pred
     | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
     | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
     | SailAST.E_vector (_, _) -> Predicate.bot_pred
     | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
     | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_vector_update_subrange (_, _, _, _, _) -> Predicate.bot_pred
     | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
     | SailAST.E_list (_, _) -> Predicate.bot_pred
     | SailAST.E_cons (tan, exp1, exp2) ->
       Predicate.bind (eq_o_i (Env.get tan))
         (fun aa ->
           (match aa with None -> Predicate.bot_pred
             | Some (_, t) ->
               Predicate.bind (check_exp_typ_i_i exp2 t)
                 (fun () ->
                   Predicate.bind (eq_o_i (Env.is_list_type tan))
                     (fun ab ->
                       (match ab with None -> Predicate.bot_pred
                         | Some elem_typ ->
                           Predicate.bind (check_exp_list_i_i [exp1] [elem_typ])
                             (fun () -> Predicate.single []))))))
     | SailAST.E_record (_, _) -> Predicate.bot_pred
     | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
     | SailAST.E_field (_, _, _) -> Predicate.bot_pred
     | SailAST.E_case (_, _, _) -> Predicate.bot_pred
     | SailAST.E_let (_, _, _) -> Predicate.bot_pred
     | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
     | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
     | SailAST.E_return (_, _) -> Predicate.bot_pred
     | SailAST.E_exit (_, _) -> Predicate.bot_pred
     | SailAST.E_ref (_, _) -> Predicate.bot_pred
     | SailAST.E_throw (_, _) -> Predicate.bot_pred
     | SailAST.E_try (_, _, _) -> Predicate.bot_pred
     | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
     | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
     | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
     | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
     | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                                       (Predicate.sup_pred
 (Predicate.bind (Predicate.single xa)
   (fun a ->
     (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
       | SailAST.E_id (_, _) -> Predicate.bot_pred
       | SailAST.E_lit (_, _) -> Predicate.bot_pred
       | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
       | SailAST.E_app (_, _, _) -> Predicate.bot_pred
       | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_tuple (_, _) -> Predicate.bot_pred
       | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
       | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
       | SailAST.E_vector (_, _) -> Predicate.bot_pred
       | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
       | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_vector_update_subrange (_, _, _, _, _) -> Predicate.bot_pred
       | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
       | SailAST.E_list (_, _) -> Predicate.bot_pred
       | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
       | SailAST.E_record (_, _) -> Predicate.bot_pred
       | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
       | SailAST.E_field (_, _, _) -> Predicate.bot_pred
       | SailAST.E_case (_, _, _) -> Predicate.bot_pred
       | SailAST.E_let (tan, lb, exp) ->
         Predicate.bind
           (Predicate.if_pred
             (trace
               [Stringa.Chara
                  (true, true, false, false, false, true, true, false);
                 Stringa.Chara
                   (false, false, false, true, false, true, true, false);
                 Stringa.Chara
                   (true, false, true, false, false, true, true, false);
                 Stringa.Chara
                   (true, true, false, false, false, true, true, false);
                 Stringa.Chara
                   (true, true, false, true, false, true, true, false);
                 Stringa.Chara
                   (true, true, true, true, true, false, true, false);
                 Stringa.Chara
                   (false, false, true, true, false, true, true, false);
                 Stringa.Chara
                   (true, false, true, false, false, true, true, false);
                 Stringa.Chara
                   (false, false, true, false, true, true, true, false);
                 Stringa.Chara
                   (true, false, false, true, false, false, true, false)]))
           (fun () ->
             Predicate.bind (eq_o_i (Env.get tan))
               (fun aa ->
                 (match aa with None -> Predicate.bot_pred
                   | Some (env, t1) ->
                     Predicate.bind (check_letbind_i_o lb)
                       (fun x ->
                         Predicate.bind
                           (check_exp_typ_env_i_i_i (add_locals env x) exp t1)
                           (fun () -> Predicate.single [])))))
       | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
       | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
       | SailAST.E_return (_, _) -> Predicate.bot_pred
       | SailAST.E_exit (_, _) -> Predicate.bot_pred
       | SailAST.E_ref (_, _) -> Predicate.bot_pred
       | SailAST.E_throw (_, _) -> Predicate.bot_pred
       | SailAST.E_try (_, _, _) -> Predicate.bot_pred
       | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
       | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
       | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
       | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
       | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
 (Predicate.sup_pred
   (Predicate.bind (Predicate.single xa)
     (fun a ->
       (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
         | SailAST.E_id (_, _) -> Predicate.bot_pred
         | SailAST.E_lit (_, _) -> Predicate.bot_pred
         | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
         | SailAST.E_app (_, _, _) -> Predicate.bot_pred
         | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
         | SailAST.E_tuple (_, _) -> Predicate.bot_pred
         | SailAST.E_if (tan, exp1, exp2, exp3) ->
           Predicate.bind (check_exp_i_o exp1)
             (fun _ ->
               Predicate.bind (eq_o_i (Env.get tan))
                 (fun aa ->
                   (match aa with None -> Predicate.bot_pred
                     | Some (env, t) ->
                       Predicate.bind (eq_o_i (Env.type_of_exp exp1))
                         (fun ab ->
                           (match ab with None -> Predicate.bot_pred
                             | Some t_exp1 ->
                               Predicate.bind
                                 (eq_o_i (Env.deconstruct_bool_type t_exp1))
                                 (fun ac ->
                                   (match ac with None -> Predicate.bot_pred
                                     | Some nc ->
                                       Predicate.bind
 (check_exp_typ_env_i_i_i (Env.add_constraint nc env) exp2 t)
 (fun () ->
   Predicate.bind
     (check_exp_typ_env_i_i_i (Env.add_constraint (nc_not nc) env) exp3 t)
     (fun () -> Predicate.single [])))))))))
         | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
         | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
         | SailAST.E_vector (_, _) -> Predicate.bot_pred
         | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
         | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
         | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
         | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
           Predicate.bot_pred
         | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
         | SailAST.E_list (_, _) -> Predicate.bot_pred
         | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
         | SailAST.E_record (_, _) -> Predicate.bot_pred
         | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
         | SailAST.E_field (_, _, _) -> Predicate.bot_pred
         | SailAST.E_case (_, _, _) -> Predicate.bot_pred
         | SailAST.E_let (_, _, _) -> Predicate.bot_pred
         | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
         | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
         | SailAST.E_return (_, _) -> Predicate.bot_pred
         | SailAST.E_exit (_, _) -> Predicate.bot_pred
         | SailAST.E_ref (_, _) -> Predicate.bot_pred
         | SailAST.E_throw (_, _) -> Predicate.bot_pred
         | SailAST.E_try (_, _, _) -> Predicate.bot_pred
         | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
         | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
         | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
         | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
         | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
         | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
   (Predicate.sup_pred
     (Predicate.bind (Predicate.single xa)
       (fun a ->
         (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
           | SailAST.E_id (_, _) -> Predicate.bot_pred
           | SailAST.E_lit (_, _) -> Predicate.bot_pred
           | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
           | SailAST.E_app (_, _, _) -> Predicate.bot_pred
           | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
           | SailAST.E_tuple (_, _) -> Predicate.bot_pred
           | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
           | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
           | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
           | SailAST.E_vector (_, _) -> Predicate.bot_pred
           | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
           | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
           | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
           | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
             Predicate.bot_pred
           | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
           | SailAST.E_list (_, _) -> Predicate.bot_pred
           | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
           | SailAST.E_record (_, _) -> Predicate.bot_pred
           | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
           | SailAST.E_field (_, _, _) -> Predicate.bot_pred
           | SailAST.E_case (_, _, _) -> Predicate.bot_pred
           | SailAST.E_let (_, _, _) -> Predicate.bot_pred
           | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
           | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
           | SailAST.E_return (_, _) -> Predicate.bot_pred
           | SailAST.E_exit (_, _) -> Predicate.bot_pred
           | SailAST.E_ref (_, _) -> Predicate.bot_pred
           | SailAST.E_throw (_, _) -> Predicate.bot_pred
           | SailAST.E_try (_, _, _) -> Predicate.bot_pred
           | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_id (_, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_deref (_, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_memory (_, _, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (tan, SailAST.LEXP_cast (_, _, _), exp1, exp2) ->
             Predicate.bind (check_exp_i_o exp1)
               (fun _ ->
                 Predicate.bind (check_exp_i_o exp2)
                   (fun _ ->
                     Predicate.bind (eq_o_i (Env.get tan))
                       (fun aa ->
                         (match aa with None -> Predicate.bot_pred
                           | Some (env, t1) ->
                             Predicate.bind (eq_o_i (Env.type_of_exp exp1))
                               (fun ab ->
                                 (match ab with None -> Predicate.bot_pred
                                   | Some t2 ->
                                     Predicate.bind (subtype_i_i_i env t1 t2)
                                       (fun () -> Predicate.single [])))))))
           | SailAST.E_var (_, SailAST.LEXP_tup (_, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_vector_concat (_, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_vector (_, _, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_vector_range (_, _, _, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_var (_, SailAST.LEXP_field (_, _, _), _, _) ->
             Predicate.bot_pred
           | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
           | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
           | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
           | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
     (Predicate.sup_pred
       (Predicate.bind (Predicate.single xa)
         (fun a ->
           (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
             | SailAST.E_id (_, _) -> Predicate.bot_pred
             | SailAST.E_lit (_, _) -> Predicate.bot_pred
             | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
             | SailAST.E_app (_, _, _) -> Predicate.bot_pred
             | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_tuple (_, _) -> Predicate.bot_pred
             | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
             | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
             | SailAST.E_vector (_, _) -> Predicate.bot_pred
             | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
             | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
               Predicate.bot_pred
             | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
             | SailAST.E_list (_, _) -> Predicate.bot_pred
             | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
             | SailAST.E_record (_, _) -> Predicate.bot_pred
             | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
             | SailAST.E_field (_, _, _) -> Predicate.bot_pred
             | SailAST.E_case (_, _, _) -> Predicate.bot_pred
             | SailAST.E_let (_, _, _) -> Predicate.bot_pred
             | SailAST.E_assign (_, lexp, exp) ->
               Predicate.bind (check_exp_i_o exp)
                 (fun _ ->
                   Predicate.bind (check_lexp_i_o lexp) Predicate.single)
             | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
             | SailAST.E_return (_, _) -> Predicate.bot_pred
             | SailAST.E_exit (_, _) -> Predicate.bot_pred
             | SailAST.E_ref (_, _) -> Predicate.bot_pred
             | SailAST.E_throw (_, _) -> Predicate.bot_pred
             | SailAST.E_try (_, _, _) -> Predicate.bot_pred
             | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
             | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
             | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
             | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
             | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
       (Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
               | SailAST.E_id (_, _) -> Predicate.bot_pred
               | SailAST.E_lit (_, _) -> Predicate.bot_pred
               | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
               | SailAST.E_app (_, _, _) -> Predicate.bot_pred
               | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_tuple (_, _) -> Predicate.bot_pred
               | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
               | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector (_, _) -> Predicate.bot_pred
               | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                 Predicate.bot_pred
               | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
               | SailAST.E_list (_, _) -> Predicate.bot_pred
               | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
               | SailAST.E_record (_, _) -> Predicate.bot_pred
               | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
               | SailAST.E_field (_, _, _) -> Predicate.bot_pred
               | SailAST.E_case (_, exp, pexps) ->
                 Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (check_pexps_i pexps)
                       (fun () ->
                         Predicate.bind (check_exp_i_o exp)
                           (fun _ -> Predicate.single [])))
               | SailAST.E_let (_, _, _) -> Predicate.bot_pred
               | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
               | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
               | SailAST.E_return (_, _) -> Predicate.bot_pred
               | SailAST.E_exit (_, _) -> Predicate.bot_pred
               | SailAST.E_ref (_, _) -> Predicate.bot_pred
               | SailAST.E_throw (_, _) -> Predicate.bot_pred
               | SailAST.E_try (_, _, _) -> Predicate.bot_pred
               | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
               | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
               | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
               | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
               | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
         (Predicate.sup_pred
           (Predicate.bind (Predicate.single xa)
             (fun a ->
               (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                 | SailAST.E_id (_, _) -> Predicate.bot_pred
                 | SailAST.E_lit (_, _) -> Predicate.bot_pred
                 | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                 | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_loop (tan, _, _, exp1, exp2) ->
                   Predicate.bind (check_exp_i_o exp1)
                     (fun _ ->
                       Predicate.bind (check_exp_i_o exp2)
                         (fun _ ->
                           Predicate.bind (eq_o_i (Env.get tan))
                             (fun aa ->
                               (match aa with None -> Predicate.bot_pred
                                 | Some (env, _) ->
                                   Predicate.bind
                                     (eq_o_i (Env.type_of_exp exp1))
                                     (fun ab ->
                                       (match ab with None -> Predicate.bot_pred
 | Some t1 ->
   Predicate.bind (eq_o_i (Env.deconstruct_bool_type t1))
     (fun ac ->
       (match ac with None -> Predicate.bot_pred
         | Some nc ->
           Predicate.bind
             (check_exp_typ_env_i_i_i (Env.add_constraint nc env) exp2
               AstUtils.unit_typ)
             (fun () -> Predicate.single [])))))))))
                 | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector (_, _) -> Predicate.bot_pred
                 | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_subrange (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                   Predicate.bot_pred
                 | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_list (_, _) -> Predicate.bot_pred
                 | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_record (_, _) -> Predicate.bot_pred
                 | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                 | SailAST.E_return (_, _) -> Predicate.bot_pred
                 | SailAST.E_exit (_, _) -> Predicate.bot_pred
                 | SailAST.E_ref (_, _) -> Predicate.bot_pred
                 | SailAST.E_throw (_, _) -> Predicate.bot_pred
                 | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                 | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                 | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                 | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
           (Predicate.sup_pred
             (Predicate.bind (Predicate.single xa)
               (fun a ->
                 (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                   | SailAST.E_id (_, _) -> Predicate.bot_pred
                   | SailAST.E_lit (_, _) -> Predicate.bot_pred
                   | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                   | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_for (_, _, exp1, exp2, exp3, _, exp4) ->
                     Predicate.bind (check_exp_typ_i_i exp1 AstUtils.int_typ)
                       (fun () ->
                         Predicate.bind
                           (check_exp_typ_i_i exp2 AstUtils.int_typ)
                           (fun () ->
                             Predicate.bind
                               (check_exp_typ_i_i exp3 AstUtils.int_typ)
                               (fun () ->
                                 Predicate.bind
                                   (check_exp_typ_i_i exp4 AstUtils.unit_typ)
                                   (fun () -> Predicate.single []))))
                   | SailAST.E_vector (_, _) -> Predicate.bot_pred
                   | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_vector_subrange (_, _, _, _) ->
                     Predicate.bot_pred
                   | SailAST.E_vector_update (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                     Predicate.bot_pred
                   | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_list (_, _) -> Predicate.bot_pred
                   | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_record (_, _) -> Predicate.bot_pred
                   | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                   | SailAST.E_return (_, _) -> Predicate.bot_pred
                   | SailAST.E_exit (_, _) -> Predicate.bot_pred
                   | SailAST.E_ref (_, _) -> Predicate.bot_pred
                   | SailAST.E_throw (_, _) -> Predicate.bot_pred
                   | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                   | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_internal_plet (_, _, _, _) -> Predicate.bot_pred
                   | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                   | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                   | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
             (Predicate.sup_pred
               (Predicate.bind (Predicate.single xa)
                 (fun a ->
                   (match a with SailAST.E_block (_, []) -> Predicate.bot_pred
                     | SailAST.E_block (tan, [exp]) ->
                       Predicate.bind (eq_o_i (Env.get tan))
                         (fun aa ->
                           (match aa with None -> Predicate.bot_pred
                             | Some (_, t) ->
                               Predicate.bind (check_exp_typ_i_i exp t)
                                 (fun () ->
                                   Predicate.bind
                                     (Predicate.if_pred
                                       (trace
 ([Stringa.Chara (false, true, false, false, false, true, true, false);
    Stringa.Chara (false, false, true, true, false, true, true, false);
    Stringa.Chara (true, true, true, true, false, true, true, false);
    Stringa.Chara (true, true, false, false, false, true, true, false);
    Stringa.Chara (true, true, false, true, false, true, true, false);
    Stringa.Chara (false, false, false, false, false, true, false, false);
    Stringa.Chara (true, true, false, false, true, true, true, false);
    Stringa.Chara (true, false, false, true, false, true, true, false);
    Stringa.Chara (false, true, true, true, false, true, true, false);
    Stringa.Chara (true, true, true, false, false, true, true, false);
    Stringa.Chara (false, false, true, true, false, true, true, false);
    Stringa.Chara (true, false, true, false, false, true, true, false);
    Stringa.Chara (false, false, false, false, false, true, false, false);
    Stringa.Chara (false, false, true, false, true, true, true, false);
    Stringa.Chara (true, false, true, true, true, true, false, false)] @
   ShowAST.shows_prec_typ Arith.Zero_nat t [])))
                                     (fun () -> Predicate.single []))))
                     | SailAST.E_block (_, _ :: _ :: _) -> Predicate.bot_pred
                     | SailAST.E_id (_, _) -> Predicate.bot_pred
                     | SailAST.E_lit (_, _) -> Predicate.bot_pred
                     | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                     | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_for (_, _, _, _, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_vector (_, _) -> Predicate.bot_pred
                     | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_vector_subrange (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_update (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_list (_, _) -> Predicate.bot_pred
                     | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_record (_, _) -> Predicate.bot_pred
                     | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                     | SailAST.E_return (_, _) -> Predicate.bot_pred
                     | SailAST.E_exit (_, _) -> Predicate.bot_pred
                     | SailAST.E_ref (_, _) -> Predicate.bot_pred
                     | SailAST.E_throw (_, _) -> Predicate.bot_pred
                     | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                     | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                     | SailAST.E_internal_plet (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                     | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                     | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
               (Predicate.sup_pred
                 (Predicate.bind (Predicate.single xa)
                   (fun a ->
                     (match a with SailAST.E_block (_, []) -> Predicate.bot_pred
                       | SailAST.E_block (_, [_]) -> Predicate.bot_pred
                       | SailAST.E_block (tan, exp1 :: exp2 :: exps) ->
                         Predicate.bind (subtype_exp_i_i exp1 AstUtils.unit_typ)
                           (fun () ->
                             Predicate.bind (check_exp_i_o exp1)
                               (fun x ->
                                 Predicate.bind
                                   (check_local_binds_i_i (exp2 :: exps) x)
                                   (fun () ->
                                     Predicate.bind
                                       (check_exp_i_o
 (SailAST.E_block (tan, exp2 :: exps)))
                                       (fun _ -> Predicate.single []))))
                       | SailAST.E_id (_, _) -> Predicate.bot_pred
                       | SailAST.E_lit (_, _) -> Predicate.bot_pred
                       | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                       | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_for (_, _, _, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector (_, _) -> Predicate.bot_pred
                       | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_vector_subrange (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_list (_, _) -> Predicate.bot_pred
                       | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_record (_, _) -> Predicate.bot_pred
                       | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                       | SailAST.E_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_exit (_, _) -> Predicate.bot_pred
                       | SailAST.E_ref (_, _) -> Predicate.bot_pred
                       | SailAST.E_throw (_, _) -> Predicate.bot_pred
                       | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assert (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_internal_plet (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                       | SailAST.E_constraint (_, _) -> Predicate.bot_pred)))
                 (Predicate.bind (Predicate.single xa)
                   (fun a ->
                     (match a with SailAST.E_block (_, _) -> Predicate.bot_pred
                       | SailAST.E_id (_, _) -> Predicate.bot_pred
                       | SailAST.E_lit (_, _) -> Predicate.bot_pred
                       | SailAST.E_cast (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_app (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_app_infix (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_tuple (_, _) -> Predicate.bot_pred
                       | SailAST.E_if (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_loop (_, _, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_for (_, _, _, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector (_, _) -> Predicate.bot_pred
                       | SailAST.E_vector_access (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_vector_subrange (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_update_subrange (_, _, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_vector_append (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_list (_, _) -> Predicate.bot_pred
                       | SailAST.E_cons (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_record (_, _) -> Predicate.bot_pred
                       | SailAST.E_record_update (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_field (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_case (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_let (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assign (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_sizeof (_, _) -> Predicate.bot_pred
                       | SailAST.E_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_exit (_, _) -> Predicate.bot_pred
                       | SailAST.E_ref (_, _) -> Predicate.bot_pred
                       | SailAST.E_throw (_, _) -> Predicate.bot_pred
                       | SailAST.E_try (_, _, _) -> Predicate.bot_pred
                       | SailAST.E_assert (_, assert_exp, _) ->
                         Predicate.bind (check_exp_i_o assert_exp)
                           (fun _ ->
                             Predicate.bind
                               (eq_o_i (Env.type_of_exp assert_exp))
                               (fun aa ->
                                 (match aa with None -> Predicate.bot_pred
                                   | Some _ -> Predicate.single [])))
                       | SailAST.E_var (_, _, _, _) -> Predicate.bot_pred
                       | SailAST.E_internal_plet (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.E_internal_return (_, _) -> Predicate.bot_pred
                       | SailAST.E_internal_value (_, _) -> Predicate.bot_pred
                       | SailAST.E_constraint (_, _) ->
                         Predicate.bot_pred)))))))))))))))))))))))))))
and check_pexp_i
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a
               with SailAST.Pat_exp (_, pat, exp) ->
                 Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (eq_o_i (env_of exp))
                       (fun aa ->
                         (match aa with None -> Predicate.bot_pred
                           | Some env ->
                             Predicate.bind (check_pat_i_o pat)
                               (fun x ->
                                 Predicate.bind
                                   (Predicate.if_pred (locals_in env x))
                                   (fun () ->
                                     Predicate.bind (check_exp_i_o exp)
                                       (fun _ -> Predicate.single ()))))))
               | SailAST.Pat_when (_, _, _, _) -> Predicate.bot_pred)))
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with SailAST.Pat_exp (_, _, _) -> Predicate.bot_pred
               | SailAST.Pat_when (_, pat, expg, exp) ->
                 Predicate.bind (eq_o_i (env_of exp))
                   (fun aa ->
                     (match aa with None -> Predicate.bot_pred
                       | Some env ->
                         Predicate.bind (check_pat_i_o pat)
                           (fun x ->
                             Predicate.bind
                               (Predicate.if_pred (locals_in env x))
                               (fun () ->
                                 Predicate.bind (check_exp_i_o exp)
                                   (fun _ ->
                                     Predicate.bind (eq_o_i (env_of expg))
                                       (fun ab ->
 (match ab with None -> Predicate.bot_pred
   | Some envg ->
     Predicate.bind (Predicate.if_pred (locals_in envg x))
       (fun () ->
         Predicate.bind (check_exp_i_o expg)
           (fun _ -> Predicate.single ()))))))))))))
and check_pexps_i
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with [] -> Predicate.single ()
               | _ :: _ -> Predicate.bot_pred)))
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with [] -> Predicate.bot_pred
               | pexp :: pexps ->
                 Predicate.bind (check_pexps_i pexps)
                   (fun () ->
                     Predicate.bind (check_pexp_i pexp)
                       (fun () -> Predicate.single ())))))
and check_exp_typ_i_i
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (exp, typ) ->
        Predicate.bind (subtype_exp_i_i exp typ)
          (fun () ->
            Predicate.bind (check_exp_i_o exp) (fun _ -> Predicate.single ())))
and check_fexp_i_i
  xa xb =
    Predicate.bind (Predicate.single (xa, xb))
      (fun (SailAST.FE_Fexp (_, x, exp), rtyp) ->
        Predicate.bind (eq_o_i (Env.deconstruct_record_type rtyp))
          (fun a ->
            (match a with None -> Predicate.bot_pred
              | Some recid ->
                Predicate.bind (eq_o_i (Env.get_env_exp exp))
                  (fun aa ->
                    (match aa with None -> Predicate.bot_pred
                      | Some env ->
                        Predicate.bind
                          (eq_o_i (Env.lookup_record_field_env env recid x))
                          (fun ab ->
                            (match ab with None -> Predicate.bot_pred
                              | Some t2 ->
                                Predicate.bind (check_exp_typ_i_i exp t2)
                                  (fun () -> Predicate.single ()))))))))
and check_fexp_list_i_i
  xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (xa, xb))
        (fun a ->
          (match a with ([], _) -> Predicate.single ()
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (xa, xb))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (fexp :: fexp_list, typ) ->
              Predicate.bind (check_fexp_list_i_i fexp_list typ)
                (fun () ->
                  Predicate.bind (check_fexp_i_i fexp typ)
                    (fun () -> Predicate.single ())))))
and check_lexp_i_o
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a
               with SailAST.LEXP_id (tan, x) ->
                 Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (false, true, false, false, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind
                       (eq_i_i (Option.equal_option SailAST.equal_typ) None
                         (Env.lookup_mutable tan x))
                       (fun () ->
                         Predicate.bind (eq_o_i (Env.get tan))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some (_, t) ->
                                 Predicate.single [(x, (Env.Mutable, t))]))))
               | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
               | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
               | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
               | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
               | SailAST.LEXP_vector_concat (_, _) -> Predicate.bot_pred
               | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
               | SailAST.LEXP_vector_range (_, _, _, _) -> Predicate.bot_pred
               | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
         (Predicate.sup_pred
           (Predicate.bind (Predicate.single xa)
             (fun a ->
               (match a
                 with SailAST.LEXP_id (tan, x) ->
                   Predicate.bind
                     (Predicate.if_pred
                       (trace
                         [Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                           Stringa.Chara
                             (false, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (false, false, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, true, true, true, true,
                               false);
                           Stringa.Chara
                             (false, false, false, false, true, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (true, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (false, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, false, true,
                               false)]))
                     (fun () ->
                       Predicate.bind
                         (Predicate.if_pred
                           (trace
                             [Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                               Stringa.Chara
                                 (false, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, true, true, true, false, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, false, false, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, true, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, true, false, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, true, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, false, true, true, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, true, true, true,
                                   false);
                               Stringa.Chara
                                 (true, false, true, false, false, true, true,
                                   false);
                               Stringa.Chara
                                 (false, false, false, false, false, true,
                                   false, false);
                               Stringa.Chara
                                 (true, true, true, true, false, true, true,
                                   false);
                               Stringa.Chara
                                 (true, true, false, true, false, true, true,
                                   false)]))
                         (fun () ->
                           Predicate.bind (eq_o_i (Env.get tan))
                             (fun aa ->
                               (match aa with None -> Predicate.bot_pred
                                 | Some (env, t1) ->
                                   Predicate.bind
                                     (eq_o_i (Env.lookup_mutable tan x))
                                     (fun ab ->
                                       (match ab with None -> Predicate.bot_pred
 | Some t2 ->
   Predicate.bind
     (Predicate.if_pred
       (trace
         ([Stringa.Chara (true, true, false, false, false, true, true, false);
            Stringa.Chara (false, false, false, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, false, false, false, true, true, false);
            Stringa.Chara (true, true, false, true, false, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, false, true, true, false);
            Stringa.Chara (false, false, false, true, true, true, true, false);
            Stringa.Chara (false, false, false, false, true, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (true, false, false, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara (true, true, true, true, true, false, true, false);
            Stringa.Chara (false, true, false, false, false, true, true, false);
            Stringa.Chara (true, false, false, true, false, false, true, false);
            Stringa.Chara
              (false, false, false, false, false, true, false, false);
            Stringa.Chara (false, true, true, false, false, true, true, false);
            Stringa.Chara (true, true, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara (false, true, true, true, false, true, true, false);
            Stringa.Chara (false, false, true, false, false, true, true, false);
            Stringa.Chara
              (false, false, false, false, false, true, false, false);
            Stringa.Chara (true, false, true, true, false, true, true, false);
            Stringa.Chara (true, false, true, false, true, true, true, false);
            Stringa.Chara
              (false, false, true, false, true, true, true, false)] @
           ShowAST.shows_prec_typ Arith.Zero_nat t2 [])))
     (fun () ->
       Predicate.bind (subtype_i_i_i env t1 t2)
         (fun () -> Predicate.single []))))))))
                 | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                 | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                 | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
                 | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                 | SailAST.LEXP_vector_concat (_, _) -> Predicate.bot_pred
                 | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                 | SailAST.LEXP_vector_range (_, _, _, _) -> Predicate.bot_pred
                 | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
           (Predicate.sup_pred
             (Predicate.bind (Predicate.single xa)
               (fun a ->
                 (match a with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                   | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                   | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                   | SailAST.LEXP_cast (tan, t2, x) ->
                     Predicate.bind
                       (eq_i_i (Option.equal_option SailAST.equal_typ) None
                         (Env.lookup_mutable tan x))
                       (fun () ->
                         Predicate.bind (eq_o_i (Env.get tan))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some (env, t) ->
                                 Predicate.bind (subtype_i_i_i env t2 t)
                                   (fun () ->
                                     Predicate.single
                                       [(x, (Env.Mutable, t2))]))))
                   | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                   | SailAST.LEXP_vector_concat (_, _) -> Predicate.bot_pred
                   | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                   | SailAST.LEXP_vector_range (_, _, _, _) ->
                     Predicate.bot_pred
                   | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
             (Predicate.sup_pred
               (Predicate.bind (Predicate.single xa)
                 (fun a ->
                   (match a with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                     | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                     | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                     | SailAST.LEXP_cast (tan, t, x) ->
                       Predicate.bind (eq_o_i (Env.get tan))
                         (fun aa ->
                           (match aa with None -> Predicate.bot_pred
                             | Some (env, ta) ->
                               Predicate.bind (subtype_i_i_i env ta t)
                                 (fun () ->
                                   Predicate.bind
                                     (eq_o_i (Env.lookup_mutable tan x))
                                     (fun ab ->
                                       (match ab with None -> Predicate.bot_pred
 | Some taa ->
   Predicate.bind (subtype_i_i_i env t taa) (fun () -> Predicate.single []))))))
                     | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                     | SailAST.LEXP_vector_concat (_, _) -> Predicate.bot_pred
                     | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                     | SailAST.LEXP_vector_range (_, _, _, _) ->
                       Predicate.bot_pred
                     | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
               (Predicate.sup_pred
                 (Predicate.bind (Predicate.single xa)
                   (fun a ->
                     (match a with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                       | SailAST.LEXP_deref (tan, exp) ->
                         Predicate.bind (eq_o_i (Env.get tan))
                           (fun aa ->
                             (match aa with None -> Predicate.bot_pred
                               | Some (_, _) ->
                                 Predicate.bind (check_exp_i_o exp)
                                   (fun _ ->
                                     Predicate.bind
                                       (eq_o_i (Env.type_of_exp exp))
                                       (fun ab ->
 (match ab with None -> Predicate.bot_pred
   | Some t ->
     Predicate.bind (eq_o_i (Env.deconstruct_register_type t))
       (fun ac ->
         (match ac with None -> Predicate.bot_pred
           | Some t1 ->
             Predicate.bind (subtype_tan_i_i t1 tan)
               (fun () -> Predicate.single []))))))))
                       | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                       | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
                       | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                       | SailAST.LEXP_vector_concat (_, _) -> Predicate.bot_pred
                       | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                       | SailAST.LEXP_vector_range (_, _, _, _) ->
                         Predicate.bot_pred
                       | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
                 (Predicate.sup_pred
                   (Predicate.bind (Predicate.single xa)
                     (fun a ->
                       (match a
                         with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                         | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                         | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                         | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
                         | SailAST.LEXP_tup (tan, lexps) ->
                           Predicate.bind
                             (Predicate.if_pred
                               (trace
                                 [Stringa.Chara
                                    (true, true, false, false, false, true,
                                      true, false);
                                   Stringa.Chara
                                     (false, false, false, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, false, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (false, false, true, true, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, false, false, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, true, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, true, true, true, true, false, true,
                                       false);
                                   Stringa.Chara
                                     (false, false, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, true, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (false, false, false, false, true, true,
                                       true, false);
                                   Stringa.Chara
                                     (true, false, false, true, false, false,
                                       true, false)]))
                             (fun () ->
                               Predicate.bind (eq_o_i (Env.get tan))
                                 (fun aa ->
                                   (match aa with None -> Predicate.bot_pred
                                     | Some (_, _) ->
                                       Predicate.bind
 (check_lexp_list_i_o lexps)
 (fun x ->
   Predicate.bind (eq_o_i (Lista.those (Lista.map Env.type_of_lexp lexps)))
     (fun ab ->
       (match ab with None -> Predicate.bot_pred
         | Some ts1 ->
           Predicate.bind
             (Predicate.if_pred
               (trace
                 ([Stringa.Chara
                     (true, true, false, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, false, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, false, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, false, true, false, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, true, false, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (false, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, true, true, true, true, false, true, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, false, false, true, false);
                    Stringa.Chara
                      (false, false, false, false, false, true, false, false);
                    Stringa.Chara
                      (false, false, true, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, false, true, true, true, true, false);
                    Stringa.Chara
                      (false, false, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, true, false, false, true, true, false);
                    Stringa.Chara
                      (true, true, false, false, true, true, true, false);
                    Stringa.Chara
                      (true, false, true, true, true, true, false, false)] @
                   Show.shows_prec_list ShowAST.show_typ Arith.Zero_nat ts1
                     [])))
             (fun () ->
               Predicate.bind (subtype_tan_i_i (SailAST.Typ_tup ts1) tan)
                 (fun () -> Predicate.single x))))))))
                         | SailAST.LEXP_vector_concat (_, _) ->
                           Predicate.bot_pred
                         | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                         | SailAST.LEXP_vector_range (_, _, _, _) ->
                           Predicate.bot_pred
                         | SailAST.LEXP_field (_, _, _) -> Predicate.bot_pred)))
                   (Predicate.sup_pred
                     (Predicate.bind (Predicate.single xa)
                       (fun a ->
                         (match a
                           with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                           | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                           | SailAST.LEXP_memory (_, _, _) -> Predicate.bot_pred
                           | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
                           | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                           | SailAST.LEXP_vector_concat (tan, lexps) ->
                             Predicate.bind
                               (Predicate.if_pred
                                 (trace
                                   [Stringa.Chara
                                      (true, true, false, false, false, true,
true, false);
                                     Stringa.Chara
                                       (false, false, false, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, true, true, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, true, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, false, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, true, false,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, true, true, true, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, true, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, false, false, false, true,
 true, false);
                                     Stringa.Chara
                                       (false, false, true, false, true, true,
 true, false);
                                     Stringa.Chara
                                       (true, false, false, true, false, false,
 true, false)]))
                               (fun () ->
                                 Predicate.bind
                                   (eq_o_i (Env.is_vector_type tan))
                                   (fun aa ->
                                     (match aa with None -> Predicate.bot_pred
                                       | Some (_, (order, typ)) ->
 Predicate.bind (check_lexp_vector_list_i_i_i lexps order typ)
   (fun () -> Predicate.bind (check_lexp_list_i_o lexps) Predicate.single))))
                           | SailAST.LEXP_vector (_, _, _) -> Predicate.bot_pred
                           | SailAST.LEXP_vector_range (_, _, _, _) ->
                             Predicate.bot_pred
                           | SailAST.LEXP_field (_, _, _) ->
                             Predicate.bot_pred)))
                     (Predicate.sup_pred
                       (Predicate.bind (Predicate.single xa)
                         (fun a ->
                           (match a
                             with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                             | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                             | SailAST.LEXP_memory (_, _, _) ->
                               Predicate.bot_pred
                             | SailAST.LEXP_cast (_, _, _) -> Predicate.bot_pred
                             | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                             | SailAST.LEXP_vector_concat (_, _) ->
                               Predicate.bot_pred
                             | SailAST.LEXP_vector (tan, lexp, exp) ->
                               Predicate.bind
                                 (Predicate.if_pred
                                   (trace
                                     [Stringa.Chara
(true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (false, false, false, true, false, true, true, false);
                                       Stringa.Chara
 (true, false, true, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, true, false, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, false, true, true, false, true, true, false);
                                       Stringa.Chara
 (true, false, true, false, false, true, true, false);
                                       Stringa.Chara
 (false, false, false, true, true, true, true, false);
                                       Stringa.Chara
 (false, false, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, true, false, true, false);
                                       Stringa.Chara
 (false, true, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, true, false, false, true, true, false);
                                       Stringa.Chara
 (true, true, false, false, false, true, true, false);
                                       Stringa.Chara
 (false, false, true, false, true, true, true, false);
                                       Stringa.Chara
 (true, true, true, true, false, true, true, false);
                                       Stringa.Chara
 (false, true, false, false, true, true, true, false);
                                       Stringa.Chara
 (true, false, false, true, false, false, true, false)]))
                                 (fun () ->
                                   Predicate.bind
                                     (Predicate.if_pred
                                       (trace
 [Stringa.Chara (true, true, false, false, false, true, true, false);
   Stringa.Chara (false, false, false, true, false, true, true, false);
   Stringa.Chara (true, false, true, false, false, true, true, false);
   Stringa.Chara (true, true, false, false, false, true, true, false);
   Stringa.Chara (true, true, false, true, false, true, true, false);
   Stringa.Chara (true, true, true, true, true, false, true, false);
   Stringa.Chara (false, false, true, true, false, true, true, false);
   Stringa.Chara (true, false, true, false, false, true, true, false);
   Stringa.Chara (false, false, false, true, true, true, true, false);
   Stringa.Chara (false, false, false, false, true, true, true, false);
   Stringa.Chara (true, true, true, true, true, false, true, false);
   Stringa.Chara (false, true, true, false, true, true, true, false);
   Stringa.Chara (true, false, true, false, false, true, true, false);
   Stringa.Chara (true, true, false, false, false, true, true, false);
   Stringa.Chara (false, false, true, false, true, true, true, false);
   Stringa.Chara (true, true, true, true, false, true, true, false);
   Stringa.Chara (false, true, false, false, true, true, true, false);
   Stringa.Chara (true, false, false, true, false, false, true, false);
   Stringa.Chara (false, false, false, false, false, true, false, false);
   Stringa.Chara (false, true, false, false, true, true, false, false)]))
                                     (fun () ->
                                       Predicate.bind
 (check_exp_typ_i_i exp AstUtils.int_typ)
 (fun () ->
   Predicate.bind (check_lexp_i_o lexp)
     (fun x ->
       Predicate.bind (eq_o_i (Env.get tan))
         (fun aa ->
           (match aa with None -> Predicate.bot_pred
             | Some (_, typ) ->
               Predicate.bind
                 (Predicate.if_pred
                   (trace
                     ([Stringa.Chara
                         (true, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, false, true, false, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, false, true, true, false, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, true, false, true, false);
                        Stringa.Chara
                          (false, true, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, false, false, true, true, false);
                        Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, true, true, true, false, true, true, false);
                        Stringa.Chara
                          (false, true, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, false, false, true, false);
                        Stringa.Chara
                          (false, false, false, false, false, true, false,
                            false);
                        Stringa.Chara
                          (false, false, true, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, false, true, true, true, true, false);
                        Stringa.Chara
                          (false, false, false, false, true, true, true, false);
                        Stringa.Chara
                          (true, false, true, true, true, true, false, false)] @
                       ShowAST.shows_prec_typ Arith.Zero_nat typ [])))
                 (fun () ->
                   Predicate.bind (eq_o_i (Env.type_of_lexp lexp))
                     (fun ab ->
                       (match ab with None -> Predicate.bot_pred
                         | Some t ->
                           Predicate.bind
                             (Predicate.if_pred
                               (trace
                                 ([Stringa.Chara
                                     (true, true, false, false, false, true,
                                       true, false);
                                    Stringa.Chara
                                      (false, false, false, true, false, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, false, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, false, true, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, true, true, true, false,
true, false);
                                    Stringa.Chara
                                      (false, false, true, true, false, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, true, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, true, true, true, true, false,
true, false);
                                    Stringa.Chara
                                      (false, true, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, false, false, false, true,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, true, true, true, false, true,
true, false);
                                    Stringa.Chara
                                      (false, true, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, false, true, false, false,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, false, true,
false, false);
                                    Stringa.Chara
                                      (false, true, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, true, false, false, false, true,
true, false);
                                    Stringa.Chara
                                      (false, false, true, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, false, true, true, true,
true, false);
                                    Stringa.Chara
                                      (false, false, false, false, true, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, false, false, true,
true, false);
                                    Stringa.Chara
                                      (true, false, true, true, true, true,
false, false)] @
                                   ShowAST.shows_prec_typ Arith.Zero_nat t [])))
                             (fun () ->
                               Predicate.bind
                                 (eq_o_i (Env.deconstruct_vector_type t))
                                 (fun ac ->
                                   (match ac with None -> Predicate.bot_pred
                                     | Some (_, (_, typb)) ->
                                       (if SailAST.equal_typa typ typb
 then Predicate.single x else Predicate.bot_pred)))))))))))))
                             | SailAST.LEXP_vector_range (_, _, _, _) ->
                               Predicate.bot_pred
                             | SailAST.LEXP_field (_, _, _) ->
                               Predicate.bot_pred)))
                       (Predicate.sup_pred
                         (Predicate.bind (Predicate.single xa)
                           (fun a ->
                             (match a
                               with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_memory (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_cast (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_vector_concat (_, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_vector (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_vector_range
                                   (tan, lexp, exp1, exp2)
                                 -> Predicate.bind
                                      (check_exp_typ_i_i exp1 AstUtils.int_typ)
                                      (fun () ->
Predicate.bind (check_exp_typ_i_i exp2 AstUtils.int_typ)
  (fun () ->
    Predicate.bind (check_lexp_i_o lexp)
      (fun _ ->
        Predicate.bind (eq_o_i (Env.get tan))
          (fun aa ->
            (match aa with None -> Predicate.bot_pred
              | Some (_, t2) ->
                Predicate.bind (eq_o_i (Env.type_of_lexp lexp))
                  (fun ab ->
                    (match ab with None -> Predicate.bot_pred
                      | Some t1 ->
                        Predicate.bind (eq_o_i (Env.deconstruct_vector_type t1))
                          (fun ac ->
                            (match ac with None -> Predicate.bot_pred
                              | Some (_, (order, typ)) ->
                                Predicate.bind
                                  (eq_o_i (Env.deconstruct_vector_type t2))
                                  (fun ad ->
                                    (match ad with None -> Predicate.bot_pred
                                      | Some (_, (ordera, typb)) ->
(if SailAST.equal_typa typ typb && SailAST.equal_order order ordera
  then Predicate.single [] else Predicate.bot_pred))))))))))))
                               | SailAST.LEXP_field (_, _, _) ->
                                 Predicate.bot_pred)))
                         (Predicate.bind (Predicate.single xa)
                           (fun a ->
                             (match a
                               with SailAST.LEXP_id (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_deref (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_memory (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_cast (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_tup (_, _) -> Predicate.bot_pred
                               | SailAST.LEXP_vector_concat (_, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_vector (_, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_vector_range (_, _, _, _) ->
                                 Predicate.bot_pred
                               | SailAST.LEXP_field (_, _, _) ->
                                 Predicate.single [])))))))))))
and check_lexp_list_i_o
  xa = Predicate.sup_pred
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a
               with [] ->
                 Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () -> Predicate.single [])
               | _ :: _ -> Predicate.bot_pred)))
         (Predicate.bind (Predicate.single xa)
           (fun a ->
             (match a with [] -> Predicate.bot_pred
               | lexp :: lexps ->
                 Predicate.bind
                   (Predicate.if_pred
                     (trace
                       [Stringa.Chara
                          (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, false, true, true,
                             false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, true, false, false, true, true, false);
                         Stringa.Chara
                           (false, false, false, true, true, true, true, false);
                         Stringa.Chara
                           (false, false, false, false, true, true, true,
                             false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (false, false, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (false, false, true, false, true, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, true, false, true, false);
                         Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                         Stringa.Chara
                           (true, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (false, true, true, true, false, true, true, false);
                         Stringa.Chara
                           (true, true, false, false, true, true, true, false);
                         Stringa.Chara
                           (true, false, false, true, false, false, true,
                             false)]))
                   (fun () ->
                     Predicate.bind (check_lexp_list_i_o lexps)
                       (fun x ->
                         Predicate.bind (check_lexp_i_o lexp)
                           (fun xaa -> Predicate.single (xaa @ x)))))))
and check_exp_list_i_i
  xa xb =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (xa, xb))
        (fun a ->
          (match a with ([], []) -> Predicate.single ()
            | ([], _ :: _) -> Predicate.bot_pred
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (xa, xb))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (_ :: _, []) -> Predicate.bot_pred
            | (exp :: exps, typ :: typs) ->
              Predicate.bind (check_exp_list_i_i exps typs)
                (fun () ->
                  Predicate.bind (check_exp_typ_i_i exp typ)
                    (fun () -> Predicate.single ())))))
and check_exp_typ_env_i_i_i
  xa xb xc =
    Predicate.bind (Predicate.single (xa, (xb, xc)))
      (fun (env, (exp, typ)) ->
        Predicate.bind (check_exp_i_o exp)
          (fun _ ->
            Predicate.bind (eq_o_i (Env.get_e exp))
              (fun a ->
                (match a with None -> Predicate.bot_pred
                  | Some (e, t) ->
                    Predicate.bind (subtype_i_i_i env t typ)
                      (fun () ->
                        Predicate.bind (subenv_i_i env e)
                          (fun () -> Predicate.single ()))))));;

let rec check_funcls_i_i
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a
            with ([], _) ->
              Predicate.bind
                (Predicate.if_pred
                  (trace
                    [Stringa.Chara
                       (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (false, true, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (false, true, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, false, true, true, false);
                      Stringa.Chara
                        (false, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (true, true, false, false, true, true, true, false);
                      Stringa.Chara
                        (true, true, true, true, true, false, true, false);
                      Stringa.Chara
                        (true, false, true, false, false, true, true, false);
                      Stringa.Chara
                        (true, false, true, true, false, true, true, false);
                      Stringa.Chara
                        (false, false, false, false, true, true, true, false);
                      Stringa.Chara
                        (false, false, true, false, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, true, true, true, false);
                      Stringa.Chara
                        (true, false, false, true, false, false, true, false)]))
                (fun () -> Predicate.single ())
            | (_ :: _, _) -> Predicate.bot_pred)))
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with ([], _) -> Predicate.bot_pred
            | (SailAST.FCL_Funcl (_, _, SailAST.PEXP_funcl pexp) :: fs, toa) ->
              Predicate.bind (check_funcls_i_i fs toa)
                (fun () ->
                  Predicate.bind
                    (Predicate.if_pred
                      (trace
                        [Stringa.Chara
                           (true, true, false, false, false, true, true, false);
                          Stringa.Chara
                            (false, false, false, true, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, false, true, false, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (false, true, true, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, false, true, false, true, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (false, false, true, true, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, false, false, true, true, true, false);
                          Stringa.Chara
                            (true, true, true, true, true, false, true, false);
                          Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                          Stringa.Chara
                            (true, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (false, true, true, true, false, true, true, false);
                          Stringa.Chara
                            (true, true, false, false, true, true, true, false);
                          Stringa.Chara
                            (true, false, false, true, false, false, true,
                              false)]))
                    (fun () ->
                      Predicate.bind
                        (Predicate.if_pred
                          (trace
                            [Stringa.Chara
                               (true, true, false, false, false, true, true,
                                 false);
                              Stringa.Chara
                                (false, false, false, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, false, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, true, true, true, false, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, false, true, false, true, true, true,
                                  false);
                              Stringa.Chara
                                (false, true, true, true, false, true, true,
                                  false);
                              Stringa.Chara
                                (true, true, false, false, false, true, true,
                                  false);
                              Stringa.Chara
                                (false, false, true, true, false, true, true,
                                  false)]))
                        (fun () ->
                          Predicate.bind (check_pexp_i pexp)
                            (fun () -> Predicate.single ())))))));;

let rec check_sd_i_i
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a
            with (_, SailAST.SD_function (_, _, _, _, _)) -> Predicate.single ()
            | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
            | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a
              with (_, SailAST.SD_function (_, _, _, _, _)) ->
                Predicate.bot_pred
              | (_, SailAST.SD_funcl
                      (_, SailAST.FCL_Funcl (_, _, SailAST.PEXP_funcl pexp)))
                -> Predicate.bind (check_pexp_i pexp)
                     (fun () -> Predicate.single ())
              | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a
                with (_, SailAST.SD_function (_, _, _, _, _)) ->
                  Predicate.bot_pred
                | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
                | (_, SailAST.SD_variant (_, _, _)) -> Predicate.single ()
                | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a
                  with (_, SailAST.SD_function (_, _, _, _, _)) ->
                    Predicate.bot_pred
                  | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.single ()
                  | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a
                    with (_, SailAST.SD_function (_, _, _, _, _)) ->
                      Predicate.bot_pred
                    | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.single ()
                    | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a
                      with (_, SailAST.SD_function (_, _, _, _, _)) ->
                        Predicate.bot_pred
                      | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.single ()
                      | (_, SailAST.SD_end (_, _)) -> Predicate.bot_pred)))
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a
                      with (_, SailAST.SD_function (_, _, _, _, _)) ->
                        Predicate.bot_pred
                      | (_, SailAST.SD_funcl (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_variant (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_unioncl (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_mapping (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_mapcl (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.SD_end (_, _)) ->
                        Predicate.single ()))))))));;

let rec check_def_i_i
  x xa =
    Predicate.sup_pred
      (Predicate.bind (Predicate.single (x, xa))
        (fun a ->
          (match a with (_, SailAST.DEF_type _) -> Predicate.single ()
            | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
            | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
            | (_, SailAST.DEF_val _) -> Predicate.bot_pred
            | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_default _) -> Predicate.bot_pred
            | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
            | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
            | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
            | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
      (Predicate.sup_pred
        (Predicate.bind (Predicate.single (x, xa))
          (fun a ->
            (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
              | (_, SailAST.DEF_fundef
                      (SailAST.FD_function (_, _, tannot_opt, _, funcls)))
                -> Predicate.bind
                     (Predicate.if_pred
                       (trace
                         [Stringa.Chara
                            (true, true, false, false, false, true, true,
                              false);
                           Stringa.Chara
                             (false, false, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, false, true, false, true, true,
                               false);
                           Stringa.Chara
                             (true, true, true, true, true, false, true, false);
                           Stringa.Chara
                             (false, true, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, true, true, true,
                               false);
                           Stringa.Chara
                             (false, true, true, true, false, true, true,
                               false);
                           Stringa.Chara
                             (false, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (false, true, true, false, false, true, true,
                               false);
                           Stringa.Chara
                             (true, false, false, true, false, false, true,
                               false)]))
                     (fun () ->
                       Predicate.bind (check_funcls_i_i funcls tannot_opt)
                         (fun () -> Predicate.single ()))
              | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
              | (_, SailAST.DEF_val _) -> Predicate.bot_pred
              | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_default _) -> Predicate.bot_pred
              | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
              | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
              | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
              | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single (x, xa))
            (fun a ->
              (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                | (_, SailAST.DEF_mapdef _) -> Predicate.single ()
                | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
                | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single (x, xa))
              (fun a ->
                (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_val letbind) ->
                    Predicate.bind (check_letbind_i_o letbind)
                      (fun _ -> Predicate.single ())
                  | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_loop_measures (_, _)) -> Predicate.bot_pred
                  | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                  | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single (x, xa))
                (fun a ->
                  (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_spec _) -> Predicate.single ()
                    | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                    | (_, SailAST.DEF_loop_measures (_, _)) ->
                      Predicate.bot_pred
                    | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                    | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single (x, xa))
                  (fun a ->
                    (match a with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_fixity (_, _, _)) -> Predicate.single ()
                      | (_, SailAST.DEF_overload (_, _)) -> Predicate.bot_pred
                      | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_measure (_, _, _)) -> Predicate.bot_pred
                      | (_, SailAST.DEF_loop_measures (_, _)) ->
                        Predicate.bot_pred
                      | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_internal_mutrec _) -> Predicate.bot_pred
                      | (_, SailAST.DEF_pragma (_, _)) -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single (x, xa))
                    (fun a ->
                      (match a
                        with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_fixity (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_overload (_, _)) ->
                          Predicate.single ()
                        | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_measure (_, _, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_loop_measures (_, _)) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                        | (_, SailAST.DEF_internal_mutrec _) ->
                          Predicate.bot_pred
                        | (_, SailAST.DEF_pragma (_, _)) ->
                          Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single (x, xa))
                      (fun a ->
                        (match a
                          with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_fixity (_, _, _)) ->
                            Predicate.bot_pred
                          | (_, SailAST.DEF_overload (_, _)) ->
                            Predicate.bot_pred
                          | (_, SailAST.DEF_default _) -> Predicate.single ()
                          | (_, SailAST.DEF_scattered _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_measure (_, _, _)) ->
                            Predicate.bot_pred
                          | (_, SailAST.DEF_loop_measures (_, _)) ->
                            Predicate.bot_pred
                          | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                          | (_, SailAST.DEF_internal_mutrec _) ->
                            Predicate.bot_pred
                          | (_, SailAST.DEF_pragma (_, _)) ->
                            Predicate.bot_pred)))
                    (Predicate.sup_pred
                      (Predicate.bind (Predicate.single (x, xa))
                        (fun a ->
                          (match a
                            with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_fixity (_, _, _)) ->
                              Predicate.bot_pred
                            | (_, SailAST.DEF_overload (_, _)) ->
                              Predicate.bot_pred
                            | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                            | (env, SailAST.DEF_scattered sd) ->
                              Predicate.bind (check_sd_i_i env sd)
                                (fun () -> Predicate.single ())
                            | (_, SailAST.DEF_measure (_, _, _)) ->
                              Predicate.bot_pred
                            | (_, SailAST.DEF_loop_measures (_, _)) ->
                              Predicate.bot_pred
                            | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                            | (_, SailAST.DEF_internal_mutrec _) ->
                              Predicate.bot_pred
                            | (_, SailAST.DEF_pragma (_, _)) ->
                              Predicate.bot_pred)))
                      (Predicate.sup_pred
                        (Predicate.bind (Predicate.single (x, xa))
                          (fun a ->
                            (match a
                              with (_, SailAST.DEF_type _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_fundef _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_mapdef _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_fixity (_, _, _)) ->
                                Predicate.bot_pred
                              | (_, SailAST.DEF_overload (_, _)) ->
                                Predicate.bot_pred
                              | (_, SailAST.DEF_default _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_scattered _) ->
                                Predicate.bot_pred
                              | (_, SailAST.DEF_measure (_, _, _)) ->
                                Predicate.single ()
                              | (_, SailAST.DEF_loop_measures (_, _)) ->
                                Predicate.bot_pred
                              | (_, SailAST.DEF_reg_dec _) -> Predicate.bot_pred
                              | (_, SailAST.DEF_internal_mutrec _) ->
                                Predicate.bot_pred
                              | (_, SailAST.DEF_pragma (_, _)) ->
                                Predicate.bot_pred)))
                        (Predicate.sup_pred
                          (Predicate.bind (Predicate.single (x, xa))
                            (fun a ->
                              (match a
                                with (_, SailAST.DEF_type _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_fundef _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_mapdef _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                                | (_, SailAST.DEF_spec _) -> Predicate.bot_pred
                                | (_, SailAST.DEF_fixity (_, _, _)) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_overload (_, _)) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_default _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_scattered _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_measure (_, _, _)) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_loop_measures (_, _)) ->
                                  Predicate.single ()
                                | (_, SailAST.DEF_reg_dec _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_internal_mutrec _) ->
                                  Predicate.bot_pred
                                | (_, SailAST.DEF_pragma (_, _)) ->
                                  Predicate.bot_pred)))
                          (Predicate.sup_pred
                            (Predicate.bind (Predicate.single (x, xa))
                              (fun a ->
                                (match a
                                  with (_, SailAST.DEF_type _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_fundef _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_mapdef _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_val _) -> Predicate.bot_pred
                                  | (_, SailAST.DEF_spec _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_fixity (_, _, _)) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_overload (_, _)) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_default _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_scattered _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_measure (_, _, _)) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_loop_measures (_, _)) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_reg_dec _) ->
                                    Predicate.single ()
                                  | (_, SailAST.DEF_internal_mutrec _) ->
                                    Predicate.bot_pred
                                  | (_, SailAST.DEF_pragma (_, _)) ->
                                    Predicate.bot_pred)))
                            (Predicate.sup_pred
                              (Predicate.bind (Predicate.single (x, xa))
                                (fun a ->
                                  (match a
                                    with (_, SailAST.DEF_type _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_fundef _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_mapdef _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_val _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_spec _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_fixity (_, _, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_overload (_, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_default _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_scattered _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_measure (_, _, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_loop_measures (_, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_reg_dec _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_internal_mutrec _) ->
                                      Predicate.single ()
                                    | (_, SailAST.DEF_pragma (_, _)) ->
                                      Predicate.bot_pred)))
                              (Predicate.bind (Predicate.single (x, xa))
                                (fun a ->
                                  (match a
                                    with (_, SailAST.DEF_type _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_fundef _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_mapdef _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_val _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_spec _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_fixity (_, _, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_overload (_, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_default _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_scattered _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_measure (_, _, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_loop_measures (_, _)) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_reg_dec _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_internal_mutrec _) ->
                                      Predicate.bot_pred
                                    | (_, SailAST.DEF_pragma (_, _)) ->
                                      Predicate.single ())))))))))))))));;

let rec check_def x1 x2 = Predicate.holds (check_def_i_i x1 x2);;

end;; (*struct Validator*)
