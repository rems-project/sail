default Order dec

$include <prelude.sail>

register R1 : bits(64)
register R2 : bits(64)

$property
function prop('sz: range(0, 64)) -> bool = {
  let z: bits('sz) = sail_zeros(sz);
  let x: bits('sz + 64) = R1 @ z;
  let y: bits(64 + 'sz) = R2 @ z;
  let padding = sail_zeros(64) @ sail_zeros(sz);

  // A and B must be equal
  let A = x @ y;
  let B = or_vec(sail_shiftleft(padding @ x, length(y)), padding @ y);
  A == B
}
