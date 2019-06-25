default Order dec

$include <prelude.sail>

$property
function prop(x: range(0, 64)) -> bool = {
  let bv: bits(64) = sail_zeros(64 - x) @ sail_ones(x);
  if x == 32 then {
    bv == 0x0000_0000_FFFF_FFFF
  } else {
    true
  }
}
