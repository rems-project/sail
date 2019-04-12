default Order dec

$include <prelude.sail>

$option -smt_ignore_overflow
$option -smt_int_size 256

$property
function prop forall 'n 'm, 0 <= 'n <= 128 & 0 <= 'm <= 64. (x: int('m), y: int('n), z: int) -> bool = {
  let lo = -100000000000;
  let hi = 100000000000;
  if lo >= z | z >= hi then {
    return(true)
  };

  let add_mul_distrib = x * (y + z) == (x * y) + (x * z);

  add_mul_distrib
}