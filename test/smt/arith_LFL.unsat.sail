default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow

$property
function prop forall 'n, 0 <= 'n <= 128. (x: int, y: int('n), z: int) -> bool = {
  let lo = -100000000000;
  let hi = 100000000000;
  if lo >= x | x >= hi | lo >= y | y >= hi | lo >= z | z >= hi then {
    return(true)
  };

  let add_comm  = x + y == y + x;
  let add_assoc = (x + y) + z == x + (y + z);
  let add_id  = x + 0 == x;

  let mul_comm = x * y == y * x;
  let mul_assoc = (x * y) * z == x * (y * z);
  let mul_zero = x * 0 == 0;

  let add_mul_distrib = x * (y + z) == (x * y) + (x * z);

  let add_neg_zero = x + negate(x) == 0;
  let add_neg_sub  = x + negate(y) == x - y;
  let neg_neg = negate(negate(x)) == x;

  add_comm & add_assoc & add_id
  & mul_comm & mul_assoc & mul_zero
  & add_mul_distrib
  & add_neg_zero & add_neg_sub & neg_neg
}