default Order dec

$include <prelude.sail>

/* Appending two variable-width bitvectors can exceed the maximum width
   (64 by default). That overflow must be flagged, so the top bits of the
   result are always correct when it is not. */
$property
function prop(x : bits(8), a : bits(5)) -> bool = {
  let y = x @ sail_zeros(24 + unsigned(a));
  let z = y @ y;
  length(z) == 2 * length(y) & truncateLSB(z, 8) == x
}
