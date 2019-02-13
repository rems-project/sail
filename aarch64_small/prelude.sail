/* default Order dec */

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}
/* sneaky deref with no effect necessary for bitfield writes */
val _reg_deref = "reg_deref" : forall ('a : Type). register('a) -> 'a

/* this is here because if we don't have it before including vector_dec 
   we get infinite loops caused by interaction with bool/bit casts */
/* val eq_bit2 = "eq_bit" : (bit, bit) -> bool */
/* overload operator == = {eq_bit2} */



$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
$include <option.sail>
$include <vector_dec.sail>


infix 7 >>
infix 7 <<
infix 7 ^^

val operator >> = "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)
val operator << = "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
val operator ^^ = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)


infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u
infix 4 <=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)

val pow2_atom = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)
val pow2_int = "pow2" : int -> int

overload pow2 = {pow2_atom, pow2_int}


val cast cast_bool_bit : bool -> bit
function cast_bool_bit(b) = 
  match b {
    true => bitzero,
    false => bitone
  }

val cast cast_bit_bool : bit -> bool
function cast_bit_bool (b) = 
  match b {
    bitzero => false,
    bitone => true
  }




val and_bits = {c:"and_bits", _: "and_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

overload operator & = {and_bool, and_bits}


val not_vec = {c:"not_bits", _:"not_vec"} : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val eq_anything = {ocaml: "(fun (x, y) -> x = y)", lem: "eq", coq: "generic_eq", _:"eq_anything"} : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}


val neq_vec = {lem: "neq"} : forall 'n. (bits('n), bits('n)) -> bool
function neq_vec (x, y) = not_bool(eq_bits(x, y))

val neq_anything = {lem: "neq", coq: "generic_neq"} : forall ('a : Type). ('a, 'a) -> bool
function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_atom, neq_int, neq_vec, neq_anything}


/* val reg_index : reg_size -> reg_index */
/* function reg_index x = unsigned(x) */


val quotient_nat = {ocaml: "quotient", lem: "integerDiv"} : (nat, nat) -> nat
val quotient = {ocaml: "quotient", lem: "integerDiv"} : (int, int) -> int
overload quot = {quotient_nat, quotient}


val __raw_GetSlice_int = "get_slice_int" : forall 'w, 'w >= 0. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n, 'n >= 0. (atom('n), int, int) -> bits('n)
function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val to_bits : forall 'l, 'l >= 0.(implicit('l), int) -> bits('l)
function to_bits (l, n) = __raw_GetSlice_int(l, n, 0)


val xor_vec = {c: "xor_bits", _: "xor_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power = {ocaml: "int_power", lem: "pow", coq: "pow", c: "pow_int"} : (int, int) -> int

overload operator ^ = {xor_vec, int_power, concat_str}
