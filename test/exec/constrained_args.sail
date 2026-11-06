default Order dec
$include <prelude.sail>

/* A test where a couple of arguments to a function have values fixed by a constraint.

   Some of the translated ASL SME instructions are like this.  */

val test : forall 'x 'm 'n, 'x > 0 & 'n == 16 & 'm == div('n, 'x). (int('x), int('m), int('n)) -> int

function test(x, m, n) = {
  let v : bits('n) = sail_ones(n);
  let w : bits('m) = sail_ones(m);
  unsigned(v) + unsigned(w)
}

function main() -> unit = {
  assert(test(2, 8, 16) == 65535 + 255);
}
