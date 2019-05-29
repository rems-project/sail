default Order dec

$include <prelude.sail>

$property
function prop forall 'n, 1 <= 'n <= 128. (n: int('n)) -> bool = {
  let x = sail_mask(n, 0b1);
  assert(x == sail_zero_extend(0b1, n));
  true
}
