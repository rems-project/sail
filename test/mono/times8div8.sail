default Order dec
$include <prelude.sail>
$include <smt.sail>

val extzv : forall 'n 'm, 'n >= 0 & 'm >= 'n. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec)
function extzv(m,v) = sail_zero_extend(v, m)

val cast ex_int : int -> {'n, true. int('n)}
function ex_int 'n = n
val quotient = {ocaml: "quotient", lem: "integerDiv", c: "div_int"} : (int, int) -> int
overload operator / = {quotient}

/* Byte/bits size conversions are a pain */

val accept : forall 'n. (int('n), bits(8 * 'n)) -> unit

function accept (_,_) = ()

val f : forall 'n. int('n) -> unit

function f(n) = {
    assert(constraint('n in {8,16}));
    x : bits('n) = undefined;
    let 'm : {'o, true. int('o)} = ex_int(n / 8) in {
        assert(constraint(8 * 'm == 'n));
        x = replicate_bits(0b00000000,'m);
        accept(m,x);
        accept(m,replicate_bits(0b00000000,'m));
    }
}

val accept2 : forall 'n. bits('n) -> unit

function accept2 (_) = ()

val g : forall 'm 'n. (int('m), int('n), bits('n)) -> unit

function g(m,n,v) = {
  assert(constraint('m >= 0 & 'n >= 0));
  let 'o : {'p, true. int('p)} = ex_int(m / n) in {
    assert(constraint('o * 'n == 'm));
    accept2(replicate_bits(v,o))
  }
}

val run : unit -> unit

function run () = {
    f(8);
    f(16);
    g(16,8,0x12);
    g(32,32,0x12345678);
}
