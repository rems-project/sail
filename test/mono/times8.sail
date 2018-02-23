$include <smt.sail>
$include <flow.sail>
default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
overload operator < = {lt_atom, lt_int}
val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extzv : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extzv(v) = extz_vec(sizeof('m),v)
val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)
overload append = {bitvector_concat}
val bitvector_cast = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)
overload length = {bitvector_length}
val cast ex_int : int -> {'n, true. atom('n)}
function ex_int 'n = n

/* Another byte/bit size conversion */

val bar : forall 'n. atom('n) -> bits(8 * 'n) effect pure

function bar (n) = replicate_bits(0x12,n)

val foo : forall 'size, 8 * 'size >= 0. atom('size) -> bits(8 * 'size) effect {escape}

function foo(size) = {
  assert('size == 1 | 'size == 2, "size");
  return bar('size)
}

val run : unit -> unit effect {escape}

function run () = {
  assert(foo(1) == 0x12);
  assert(foo(2) == 0x1212);
}