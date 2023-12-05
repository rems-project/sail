default Order dec
$include <prelude.sail>

val f : forall 'n 'i, 'n in {1, 2} & 0 <= 'i < 16. (int('n), int('i)) -> int

function f(n, i) = {
  let v : bits('n * 8) = sail_zeros(n * 8);
  let table : vector(16, dec, int) = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16];
  let w = add_bits_int(v, table[i]);
  unsigned(w)
}

function run () -> unit = {
  assert(f(1, 5) == 11);
  assert(f(2, 5) == 11);
}
