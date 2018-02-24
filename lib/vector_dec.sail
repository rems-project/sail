$ifndef _VECTOR_DEC
$define _VECTOR_DEC

$include <flow.sail>

type bits ('n : Int) = vector('n, dec, bit)

val "eq_bit" : (bit, bit) -> bool

val eq_bits = {
  ocaml: "eq_list",
  lem: "eq_vec",
  c: "eq_bits"
} : forall 'n. (vector('n, dec, bit), vector('n, dec, bit)) -> bool

overload operator == = {eq_bit, eq_bits}

val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)

val vector_length = {
  ocaml: "length",
  lem: "length_list",
  c: "length"
} : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)

overload length = {bitvector_length, vector_length}

val "zeros" : forall 'n. atom('n) -> bits('n)

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

val truncate = {
  ocaml: "vector_truncate",
  lem: "vector_truncate",
  c: "truncate"
} : forall 'm 'n, 'm <= 'n. (vector('n, dec, bit), atom('m)) -> vector('m, dec, bit)

val mask : forall 'len 'v, 'v >= 0. (atom('len), vector('v, dec, bit)) -> vector('len, dec, bit)

function mask(len, v) = if len <= length(v) then truncate(v, len) else zero_extend(v, len)

overload operator ^ = {mask}

val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

overload append = {bitvector_concat}

/* Used for creating long bitvector literals in the C backend. */
val "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

val vector_access = {
  ocaml: "access",
  lem: "access_list_dec",
  c: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, dec, 'a), atom('m)) -> 'a

val vector_update = {
  ocaml: "update",
  lem: "update_list_dec",
  c: "vector_update"
} : forall 'n ('a : Type). (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

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
  lem: "subrange_vec_dec",
  c: "vector_subrange"
} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val vector_update_subrange = {
  ocaml: "update_subrange",
  lem: "update_subrange_vec_dec",
  c: "vector_update_subrange"
} : forall 'n 'm 'o. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

// Some ARM specific builtins

val get_slice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val set_slice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val set_slice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val unsigned = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

val signed = "sint" : forall 'n. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

$endif
