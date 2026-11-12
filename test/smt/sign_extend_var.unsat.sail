default Order dec

$include <prelude.sail>

/* Sign-extending to a variable width keeps the signed value. */
$property
function prop(x : bits(8), a : bits(4)) -> bool = {
  let y = sail_sign_extend(x, 8 + unsigned(a));
  length(y) == 8 + unsigned(a) & signed(y) == signed(x) & truncate(y, 8) == x
}
