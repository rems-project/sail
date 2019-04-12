default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow
$option -smt_int_size 256

$property
function prop forall 'n 'm, 0 <= 'n <= 128 & 0 <= 'm <= 64. (x: int('m), y: int('n), z: int) -> bool = {
  let lo = -1000;
  let hi = 1000;
  if lo >= z | z >= hi then {
    return(true)
  };

  let mul_comm = x * y == y * x;
  let mul_assoc = (x * y) * z == x * (y * z);
  let mul_zero = x * 0 == 0;

  mul_comm & mul_assoc /* & mul_zero */
}
