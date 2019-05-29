default Order dec

$include <prelude.sail>

$property
function prop forall 'n, 0 <= 'n <= 128. (n: int('n)) -> bool = {
  let x = sail_mask(n, 0b0);
  assert(x == sail_zeros(n));
  true
}
