default Order dec

$include <prelude.sail>

register R1 : bits(32)
register R2 : bits(32)

$property
function prop((): unit) -> bool = {
  let x = sail_zero_extend(R1, 64);
  let x = sail_shiftleft(x, 33);
  let y = or_vec(x, sail_zero_extend(R2, 64));
  let z = R1 @ R2;
  y == z
}