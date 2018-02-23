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


/* Decode -> int -> existential test */

val needssize : forall 'n, 'n >= 0. atom('n) -> unit effect pure

function needssize(n) = {
  let x : bits('n) = replicate_bits(0b0,n) in
  ()
}

val test : bits(2) -> unit effect {undef,escape}

function test(x) = {
  n : int = undefined;
  match x {
    0b00 => n = 1,
    0b01 => n = 2,
    0b10 => n = 4,
    0b11 => ()
  };
  let 'n2 = ex_int(n) in {
    assert(constraint('n2 >= 0));
    needssize(n2)
  }
}

val run : unit -> unit effect {undef,escape}

function run () = {
  test(0b00);
  test(0b01);
  test(0b10);
  test(0b11);
}