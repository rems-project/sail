default Order dec

$include <prelude.sail>

register R1 : bits(128)
register R2 : bits(128)

$property
function prop((): unit) -> bool = {
  let x = sail_zero_extend(R1, 256);
  let x = sail_shiftleft(x, 128);
  let y = or_vec(x, sail_zero_extend(R2, 256));
  let z = R1 @ R2;
  y == z
}