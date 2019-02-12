default Order dec

$include <prelude.sail>

val EXTZ : forall 'n 'm, 0 <= 'n <= 'm. (implicit('m), bits('n)) -> bits('m)

function EXTZ(m, x) = sail_zero_extend(x, m)

val EXTS : forall 'n 'm, 0 <= 'n <= 'm. (bits('n), implicit('m)) -> bits('m)

function EXTS(x, m) = sail_sign_extend(x, m)

val zeros : forall 'n, 'n >= 0. implicit('n) -> bits('n)

function zeros(n) = replicate_bits(0b0, n)

function main((): unit) -> unit = {
  let a: bits(64) = EXTZ(0xFF);
  let b: bits(64) = EXTS(0xFF);
  let c: bits(64) = EXTS(0xFF, 64);
  let d: bits(64) = zeros();
  let e: bits(64) = zeros(64);
  print_bits("a = ", a);
  print_bits("b = ", b);
  print_bits("c = ", c);
  print_bits("d = ", d);
  print_bits("e = ", e);
  ()
}