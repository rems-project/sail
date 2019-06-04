default Order dec

$include <prelude.sail>

$property
function prop(x: int, y: int(32), z: int) -> bool = {
  let mul_comm = x * y == y * x;
  let mul_zero1 = x * 0 == 0;
  let mul_zero2 = y * 0 == 0;

  mul_comm & mul_zero1 & mul_zero2
}