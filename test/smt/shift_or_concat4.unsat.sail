default Order dec

$include <prelude.sail>

register R1 : bits(4)
register R2 : bits(4)

$property
function prop((): unit) -> bool = {
  let x = sail_zero_extend(R1, 8);
  let x = sail_shiftleft(x, 4);
  let y = or_vec(x, sail_zero_extend(R2, 8));
  let z = R1 @ R2;
  y == z
}