$ifndef _VECTOR_INC
$define _VECTOR_INC

$include <flow.sail>

type bits ('n : Int) = vector('n, inc, bit)

val "eq_bit" : (bit, bit) -> bool

val eq_bits = {
  ocaml: "eq_list",
  lem: "eq_vec",
  c: "eq_bits",
  coq: "eq_vec"
} : forall 'n. (vector('n, inc, bit), vector('n, inc, bit)) -> bool

overload operator == = {eq_bit, eq_bits}

val bitvector_length = {coq: "length_mword", _:"length"} : forall 'n. bits('n) -> atom('n)

val vector_length = {
  ocaml: "length",
  lem: "length_list",
  c: "length",
  coq: "length_list"
} : forall 'n ('a : Type). vector('n, inc, 'a) -> atom('n)

overload length = {bitvector_length, vector_length}

val "zeros" : forall 'n. atom('n) -> bits('n)

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

val truncate = {
  ocaml: "vector_truncate",
  lem: "vector_truncate",
  coq: "vector_truncate",
  c: "truncate"
} : forall 'm 'n, 'm >= 0 & 'm <= 'n. (vector('n, inc, bit), atom('m)) -> vector('m, inc, bit)

val mask : forall 'len 'v, 'len >= 0 & 'v >= 0. (atom('len), vector('v, inc, bit)) -> vector('len, inc, bit)

function mask(len, v) = if len <= length(v) then truncate(v, len) else zero_extend(v, len)

overload operator ^ = {mask}

val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append", coq: "concat_vec"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

overload append = {bitvector_concat}

/* Used for creating long bitvector literals in the C backend. */
val "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

val bitvector_access = {
  ocaml: "access",
  lem: "access_vec_inc",
  coq: "access_vec_inc",
  c: "vector_access"
} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n . (bits('n), int('m)) -> bit

val plain_vector_access = {
  ocaml: "access",
  lem: "access_list_inc",
  coq: "access_list_inc",
  c: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), atom('m)) -> 'a

overload vector_access = {bitvector_access, plain_vector_access}

val bitvector_update = {
  ocaml: "update",
  lem: "update_vec_inc",
  coq: "update_vec_inc",
  c: "vector_update"
} : forall 'n 'm, 0 <= 'm < 'n. (bits('n), atom('m), bit) -> bits('n)

val plain_vector_update = {
  ocaml: "update",
  lem: "update_list_inc",
  coq: "update_list_inc",
  c: "vector_update"
} : forall 'n 'm ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), atom('m), 'a) -> vector('n, inc, 'a)

overload vector_update = {bitvector_update, plain_vector_update}

val add_bits = {
  ocaml: "add_vec",
  c: "add_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_bits_int = {
  ocaml: "add_vec_int",
  c: "add_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

overload operator + = {add_bits, add_bits_int}

val vector_subrange = {
  ocaml: "subrange",
  lem: "subrange_vec_inc",
  c: "vector_subrange",
  coq: "subrange_vec_inc"
} : forall ('n : Int) ('m : Int) ('o : Int), 0 <= 'm <= 'o < 'n.
  (bits('n), atom('m), atom('o)) -> bits('o - 'm + 1)

val vector_update_subrange = {
  ocaml: "update_subrange",
  lem: "update_subrange_vec_inc",
  c: "vector_update_subrange",
  coq: "update_subrange_vec_inc"
} : forall 'n 'm 'o, 0 <= 'm <= 'o < 'n. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

// Some ARM specific builtins

/*
val get_slice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val set_slice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val set_slice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)
*/

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val unsigned = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint",
  coq: "uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

/* We need a non-empty vector so that the range makes sense */
val signed = "sint" : forall 'n, 'n > 0. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

$endif
