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

/* Inlining feature test functions, as in aarch64 */

val HaveSomeFeature : unit -> bool

function HaveSomeFeature () = return(true)

val foo : bits(1) -> unit effect {escape, undef}

function foo(x) = {
  let i : int =
    match x {
    0b0 => 8,
    0b1 => if HaveSomeFeature() then 16 else undefined
    }
  in
  let 'n = i in {
    assert(constraint('n >= 0));
    let y : bits('n) = replicate_bits(0b0, n) in
    ()
  }
}

val run : unit -> unit effect {escape, undef}

function run () = {
    foo(0b0);
    foo(0b1);
}