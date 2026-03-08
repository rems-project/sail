default Order dec

$include <prelude.sail>

val EXTZ : forall 'n 'm, 0 <= 'n <= 'm. (implicit('m), bits('n)) -> bits('m)

function EXTZ(m, x) = sail_zero_extend(x, m)

val EXTS : forall 'n 'm, 0 <= 'n <= 'm. (implicit('m), bits('n)) -> bits('m)

function EXTS(m, x) = sail_sign_extend(x, m)

val zeros : forall 'n, 'n >= 0. implicit('n) -> bits('n)

function zeros(n) = replicate_bits(0b0, n)

val dzeros : forall 'n 'm, 'n >= 0 & 'm >= 0. (implicit('n), implicit('m)) -> (bits('n), bits('m))

function dzeros(n, m) = (zeros(n), zeros(m))

val dzeros2 : forall 'n 'm, 'n >= 0 & 'm >= 0. (implicit('n), implicit('m), unit) -> (bits('n), bits('m))

function dzeros2(n, m, _) = (zeros(n), zeros(m))

function main((): unit) -> unit = {
  let a: bits(64) = EXTZ(0xFF);
  let b: bits(64) = EXTS(0xFF);
  let c: bits(64) = EXTS(64, 0xFF);
  let d: bits(64) = zeros();
  let e: bits(64) = zeros(64);
  let (f, g): (bits(64), bits(32)) = dzeros();
  let (h, i) = dzeros(16, 8);
  let (j, k): (bits(4), bits(2)) = dzeros2();
  print_bits("a = ", a);
  print_bits("b = ", b);
  print_bits("c = ", c);
  print_bits("d = ", d);
  print_bits("e = ", e);
  print_bits("f = ", f);
  print_bits("g = ", g);
  print_bits("h = ", h);
  print_bits("i = ", i);
  print_bits("j = ", j);
  print_bits("k = ", k)
}