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
val quotient = {ocaml: "quotient", lem: "integerDiv", c: "div_int"} : (int, int) -> int
overload operator / = {quotient}

/* Byte/bits size conversions are a pain */

val accept : forall 'n. (atom('n), bits(8 * 'n)) -> unit

function accept (_,_) = ()

val f : forall 'n. atom('n) -> unit effect {escape,undef}

function f(n) = {
    assert(constraint('n in {8,16}));
    x : bits('n) = undefined;
    let 'm : {'o, true. atom('o)} = ex_int(n / 8) in {
        assert(constraint(8 * 'm == 'n));
        x = replicate_bits(0b00000000,'m);
        accept(m,x);
        accept(m,replicate_bits(0b00000000,'m));
    }
}

val accept2 : forall 'n. bits('n) -> unit

function accept2 (_) = ()

val g : forall 'm 'n. (atom('m), atom('n), bits('n)) -> unit effect {escape}

function g(m,n,v) = {
  assert(constraint('m >= 0 & 'n >= 0));
  let 'o : {'p, true. atom('p)} = ex_int(m / n) in {
    assert(constraint('o * 'n == 'm));
    accept2(replicate_bits(v,o))
  }
}

val run : unit -> unit effect {escape, undef}

function run () = {
    f(8);
    f(16);
    g(16,8,0x12);
    g(32,32,0x12345678);
}
