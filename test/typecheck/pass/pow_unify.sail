/* This used to produce an error when being rewritten into monadic
   form for Lem because the type checker could not unify 2 ^ 'ex1 with
   2 ^ 'ex2. */

default Order dec

$include <prelude.sail>

val f: int -> unit

val pow2 = pure "pow2" : forall 'n, 'n >= 0. int('n) -> int(2 ^ 'n)

register r: bits(32)

function f(n) = {
  m: int = n;
  assert(m >= 4 * pow2(unsigned(r[9 .. 6])) & m <= 2048);
}
