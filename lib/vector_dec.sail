$ifndef _VECTOR_DEC
$define _VECTOR_DEC

type bits ('n : Int) = vector('n, dec, bit)

val "zeros" : forall 'n. atom('n) -> bits('n)

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)
val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

/* Used for creating long bitvector literals in the C backend. */
val "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

val add_bits = {
  ocaml: "add_vec",
  c: "add_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_bits_int = {
  ocaml: "add_vec_int",
  c: "add_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

$endif
