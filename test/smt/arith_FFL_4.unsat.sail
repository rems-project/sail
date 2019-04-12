default Order dec

$include <prelude.sail>

$property
function prop forall 'n 'm, 0 <= 'n <= 128 & 0 <= 'm <= 64. (x: int('m), y: int('n), z: int) -> bool = {
  let add_neg_zero = x + negate(x) == 0;
  let add_neg_sub  = x + negate(y) == x - y;
  let neg_neg = negate(negate(x)) == x;

  add_neg_zero & add_neg_sub & neg_neg
}