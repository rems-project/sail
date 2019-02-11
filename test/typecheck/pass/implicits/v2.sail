default Order dec

$include <prelude.sail>

val EXTZ : forall 'n 'm, 0 <= 'n <= 'm. (implicit('m - 1), bits('n)) -> bits('m)

function EXTZ(m, x) = sail_zero_extend(x, m)

val EXTS : forall 'n 'm, 0 <= 'n <= 'm. (implicit('m), bits('n)) -> bits('m)

function EXTS(m, x) = sail_sign_extend(x, m)

function main((): unit) -> unit = {
  let a: bits(64) = EXTZ(0xFF);
  let b: bits(64) = EXTS(0xFF);
  print_bits("a = ", a);
  print_bits("b = ", b)
}