default Order dec
type bits ('n : Int) = vector('n, dec, bit)

union option ('a : Type) = {None : unit, Some : 'a}

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec", c: "vector_subrange"}
		    : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm & 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val bitvector_access = {ocaml: "access", lem: "access_vec_dec", c: "vector_access"}
		     : forall ('n : Int) ('m : Int), 0 <= 'm & 'm + 1 <= 'n.
  (bits('n), atom('m)) -> bit

overload vector_access = {bitvector_access}

val eq_bit = {ocaml: "eq_bit", lem: "eq", interpreter: "eq_anything", c: "eq_bit"}: (bit, bit) -> bool

overload operator == = {
  eq_bit
}

val and_bool = {ocaml: "and_bool", lem: "and_bool", smt: "and_bool", interpreter: "and_bool", c: "and_bool"}: (bool, bool) -> bool


////////////////////////////////////////////////////////////

val works : bits(8) -> bits(3)
function works bv = match bv {
  a : bits(3) @ b : bits(2) @ 0b000 => a
}

val doesnt : bits(8) -> bits(3)
function doesnt bv = match bv {
  (a : bits(3) @ b : bits(2)) @ 0b000 => a
}

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val main : unit -> unit

function main() = {
  print_bits("works = ", works(0b1010_0000));
  print_bits("doesnt = ", doesnt(0b0101_0000));
}