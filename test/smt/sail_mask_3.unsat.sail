default Order dec

$include <prelude.sail>

$property
function prop forall 'n, 32 <= 'n <= 128. (n: int('n)) -> bool = {
  let x = sail_mask(n, 0xdeadbeef);
  assert(x == sail_zero_extend(0xdeadbeef, n));
  true
}
