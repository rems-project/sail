default Order dec
$include <prelude.sail>
$include <smt.sail>
val "extz_vec" : forall 'n 'm. (atom('m),bitvector('n, dec)) -> bitvector('m, dec) effect pure
val extzv : forall 'n 'm. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extzv(m,v) = extz_vec(m,v)
val bitvector_cast = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
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
