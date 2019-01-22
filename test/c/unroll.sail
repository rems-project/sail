default Order dec

$include <prelude.sail>

/* It's hard to test that this optimization does the right thing, but
we can at least test that it doesn't do the wrong thing. */

$optimize unroll 20
val fac : forall 'n, 'n >= 0. int('n) -> int
function fac(n) = {
  if n == 0 then {
    1
  } else {
    n * fac(n - 1)
  }
}

$optimize unroll 2
val fac2 : forall 'n, 'n >= 0. int('n) -> int
function fac2(n) = {
  if n == 0 then {
    1
  } else {
    n * fac2(n - 1)
  }
}

val "print_int" : (string, int) -> unit

function main((): unit) -> unit = {
  print_int("fac(4) = ", fac(4));
  print_int("fac(5) = ", fac(5));
  print_int("fac(6) = ", fac(6));
  print_int("fac2(4) = ", fac2(4));
  print_int("fac2(5) = ", fac2(5));
  print_int("fac2(6) = ", fac2(6))
}