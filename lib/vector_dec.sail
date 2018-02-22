$ifndef _VECTOR_DEC
$define _VECTOR_DEC

type bits ('n : Int) = vector('n, dec, bit)

val "zeros" : forall 'n. atom('n) -> bits('n)

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)
val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

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

$endif
