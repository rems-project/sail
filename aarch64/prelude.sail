default Order dec

$include <smt.sail>
$include <flow.sail>

type bits ('n : Int) = vector('n, dec, bit)

val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool

val eq_string = {ocaml: "eq_string", lem: "eq"} : (string, string) -> bool

val eq_real = {ocaml: "eq_real", lem: "eq"} : (real, real) -> bool

val eq_anything = {
  ocaml: "(fun (x, y) -> x = y)",
  interpreter: "eq_anything",
  lem: "eq"
} : forall ('a : Type). ('a, 'a) -> bool

val bitvector_length = {ocaml: "length", lem: "length"} : forall 'n. bits('n) -> atom('n)
val vector_length = {ocaml: "length", lem: "length_list"} : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)
val list_length = {ocaml: "length", lem: "length_list"} : forall ('a : Type). list('a) -> int

overload length = {bitvector_length, vector_length, list_length}

overload operator == = {eq_vec, eq_string, eq_real, eq_anything}

val vector_subrange_A = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val vector_subrange_B = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int).
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

overload vector_subrange = {vector_subrange_A, vector_subrange_B}

val bitvector_access_A = {ocaml: "access", lem: "access_vec_dec"} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n.
  (bits('n), atom('m)) -> bit

val bitvector_access_B = {ocaml: "access", lem: "access_vec_dec"} : forall ('n : Int).
  (bits('n), int) -> bit

val vector_access_A = {ocaml: "access", lem: "access_list_dec"} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n.
  (vector('n, dec, 'a), atom('m)) -> 'a

val vector_access_B = {ocaml: "access", lem: "access_list_dec"} : forall ('n : Int) ('a : Type).
  (vector('n, dec, 'a), int) -> 'a

overload vector_access = {bitvector_access_A, bitvector_access_B, vector_access_A, vector_access_B}

val bitvector_update_B = {ocaml: "update", lem: "update_vec_dec"} : forall 'n.
  (bits('n), int, bit) -> bits('n)

val vector_update_B = {ocaml: "update", lem: "update_list_dec"} : forall 'n ('a : Type).
  (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

overload vector_update = {bitvector_update_B, vector_update_B}

val vector_update_subrange = {ocaml: "update_subrange", lem: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vcons : forall ('n : Int) ('a : Type).
  ('a, vector('n, dec, 'a)) -> vector('n + 1, dec, 'a)

val bitvector_concat = {ocaml: "append", lem: "concat_vec"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

val vector_concat = {ocaml: "append", lem: "append_list"} : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

overload append = {bitvector_concat, vector_concat}

val not_vec = "not_vec" : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val neq_int = {lem: "neq"} : (int, int) -> bool

function neq_int (x, y) = not_bool(eq_int(x, y))

val neq_vec = {lem: "neq_vec"} : forall 'n. (bits('n), bits('n)) -> bool

function neq_vec (x, y) = not_bool(eq_vec(x, y))

val neq_anything = {lem: "neq"} : forall ('a : Type). ('a, 'a) -> bool

function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_atom, neq_int, neq_vec, neq_anything}

val builtin_and_vec = {ocaml: "and_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val and_vec = {lem: "and_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

function and_vec (xs, ys) = builtin_and_vec(xs, ys)

overload operator & = {and_bool, and_vec}

val builtin_or_vec = {ocaml: "or_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val or_vec = {lem: "or_vec"}: forall 'n. (bits('n), bits('n)) -> bits('n)

function or_vec (xs, ys) = builtin_or_vec(xs, ys)

overload operator | = {or_bool, or_vec}

val UInt = "uint" : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

val SInt = "sint" : forall 'n. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

val hex_slice = "hex_slice" : forall 'n 'm. (string, atom('n), atom('m)) -> bits('n - 'm)

val __SetSlice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __ShiftLeft = "shiftl" : forall 'm. (bits('m), int) -> bits('m)

val __SignExtendSlice = {lem: "exts_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice = {lem: "extz_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec b =
  match b {
    bitzero => 0b0,
    bitone  => 0b1
  }

val print = "prerr_endline" : string -> unit

val putchar = "putchar" : forall ('a : Type). 'a -> unit

val concat_str = {ocaml: "concat_str", lem: "stringAppend"} : (string, string) -> string

val DecStr : int -> string

val HexStr : int -> string

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = "xor_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power = {lem: "pow"} : (int, int) -> int

val real_power = {ocaml: "real_power", lem: "realPowInteger"} : (real, int) -> real

overload operator ^ = {xor_vec, int_power, real_power}

val add_range = {ocaml: "add_int", lem: "integerAdd"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = {ocaml: "add_int", lem: "integerAdd"} : (int, int) -> int

val add_vec = "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val add_real = {ocaml: "add_real", lem: "realAdd"} : (real, real) -> real

overload operator + = {add_range, add_int, add_vec, add_vec_int, add_real}

val sub_range = {ocaml: "sub_int", lem: "integerMinus"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val sub_int = {ocaml: "sub_int", lem: "integerMinus"} : (int, int) -> int

val "sub_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val "sub_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val sub_real = {ocaml: "sub_real", lem: "realMinus"} : (real, real) -> real

val negate_range = {ocaml: "negate", lem: "integerNegate"} : forall 'n 'm. range('n, 'm) -> range(- 'm, - 'n)

val negate_int = {ocaml: "negate", lem: "integerNegate"} : int -> int

val negate_real = {ocaml: "negate_real", lem: "realNegate"} : real -> real

overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int, sub_real}

overload negate = {negate_range, negate_int, negate_real}

val mult_range = {ocaml: "mult", lem: "integerMult"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n * 'o, 'm * 'p)

val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int

val mult_real = {ocaml: "mult_real", lem: "realMult"} : (real, real) -> real

overload operator * = {mult_range, mult_int, mult_real}

val Sqrt = {ocaml: "sqrt_real", lem: "realSqrt"} : real -> real

val gteq_real = {ocaml: "gteq_real", lem: "gteq"} : (real, real) -> bool

overload operator >= = {gteq_atom, gteq_int, gteq_real}

val lteq_real = {ocaml: "lteq_real", lem: "lteq"} : (real, real) -> bool

overload operator <= = {lteq_atom, lteq_int, lteq_real}

val gt_real = {ocaml: "gt_real", lem: "gt"} : (real, real) -> bool

overload operator > = {gt_atom, gt_int, gt_real}

val lt_real = {ocaml: "lt_real", lem: "lt"} : (real, real) -> bool

overload operator < = {lt_atom, lt_int, lt_real}

val RoundDown = {ocaml: "round_down", lem: "realFloor"} : real -> int

val RoundUp = {ocaml: "round_up", lem: "realCeiling"} : real -> int

val abs_int = "abs_int" : int -> int

val abs_real = "abs_real" : real -> real

overload abs = {abs, abs_int, abs_real}

val quotient_nat = {ocaml: "quotient", lem: "integerDiv"} : (nat, nat) -> nat

val quotient_real = {ocaml: "quotient_real", lem: "realDiv"} : (real, real) -> real

val quotient = {ocaml: "quotient", lem: "integerDiv"} : (int, int) -> int

overload operator / = {quotient_nat, quotient, quotient_real}

val modulus = {ocaml: "modulus", lem: "hardware_mod"} : (int, int) -> int

overload operator % = {modulus}

val Real = {ocaml: "to_real", lem: "realFromInteger"} : int -> real

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

val min_nat = {ocaml: "min_int", lem: "min"} : (nat, nat) -> nat

val min_int = {ocaml: "min_int", lem: "min"} : (int, int) -> int

val max_nat = {ocaml: "max_int", lem: "max"} : (nat, nat) -> nat

val max_int = {ocaml: "max_int", lem: "max"} : (int, int) -> int

overload min = {min_nat, min_int}

overload max = {max_nat, max_int}

val __WriteRAM = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __ReadRAM = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n)

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val cast ex_nat : nat -> {'n, 'n >= 0. atom('n)}

function ex_nat 'n = n

val cast ex_int : int -> {'n, true. atom('n)}

function ex_int 'n = n

val ex_range : forall 'n 'm.
  range('n, 'm) -> {'o, 'n <= 'o & 'o <= 'm. atom('o)}

val coerce_int_nat : int -> nat effect {escape}

function coerce_int_nat 'x = {
  assert(constraint('x >= 0));
  x
}

val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

val pow2 = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)

val print_int = "print_int" : (string, int) -> unit
val print_bits = "print_bits" : forall 'n. (string, bits('n)) -> unit
val break : unit -> unit

function break () = ()

union exception = {
  Error_Undefined,
  Error_See : string,
  Error_Implementation_Defined : string,
  Error_ReservedEncoding
}

/*
union option ('a : Type) = {
  None,
  Some : 'a
}
*/
