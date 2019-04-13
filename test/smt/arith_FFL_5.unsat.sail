default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow
// CVC4 Really doesn't like it when this isn't 64
$option -smt_int_size 64

$property
function prop forall 'n 'm, 0 <= 'n <= 128 & 0 <= 'm <= 64. (x: int('m), y: int('n), z: int) -> bool = {
  let lo = -1000;
  let hi = 1000;
  if lo >= z | z >= hi then {
    return(true)
  };

  let mul_assoc = (x * y) * z == x * (y * z);

  mul_assoc
}
