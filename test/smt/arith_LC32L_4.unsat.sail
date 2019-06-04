default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int(32)) -> bool = {
  let add_neg_zero = x + negate(x) == 0;
  let add_neg_sub  = x + negate(y) == x - y;
  let neg_neg = negate(negate(x)) == x;

  add_neg_zero & add_neg_sub & neg_neg
}
