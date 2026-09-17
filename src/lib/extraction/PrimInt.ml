open BinInt

(** val eq_int : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let eq_int =
  Z.eqb

(** val lt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let lt =
  Z.ltb

(** val gt : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let gt =
  Z.gtb

(** val lteq : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let lteq =
  Z.leb

(** val gteq : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let gteq =
  Z.geb

(** val add_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let add_int =
  Z.add

(** val sub_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let sub_int =
  Z.sub

(** val sub_nat :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let sub_nat x y =
  Z.max Big_int_Z.zero_big_int (Z.sub x y)

(** val mult : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let mult =
  Z.mul

(** val negate : Big_int_Z.big_int -> Big_int_Z.big_int **)

let negate =
  Z.opp

(** val abs_int : Big_int_Z.big_int -> Big_int_Z.big_int **)

let abs_int =
  Z.abs

(** val max_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let max_int =
  Z.max

(** val min_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let min_int =
  Z.min

(** val quotient :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let quotient x y =
  Z.mul (Z.sgn y) (Z.div x (Z.abs y))

(** val modulus :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let modulus x y =
  Z.modulo x (Z.abs y)

(** val tdiv_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let tdiv_int =
  Z.quot

(** val tmod_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let tmod_int =
  Z.rem

(** val int_power :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let int_power =
  Z.pow

(** val pow2 : Big_int_Z.big_int -> Big_int_Z.big_int **)

let pow2 x =
  Z.pow (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) x

(** val shl_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let shl_int =
  Z.shiftl

(** val shr_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let shr_int =
  Z.shiftr

(** val lor_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let lor_int =
  Z.coq_lor

(** val land_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let land_int =
  Z.coq_land

(** val lxor_int :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let lxor_int =
  Z.coq_lxor
