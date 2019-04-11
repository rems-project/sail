default Order dec

$include <prelude.sail>

$property
function prop(xs: bits(16)) -> bool = {
  var p: bool = true;
  if xs[15] == bitzero then {
    p = 0x0000 @ xs == sail_sign_extend(xs, 32);
  } else {
    p = 0xFFFF @ xs == sail_sign_extend(xs, 32);
  };
  p
}