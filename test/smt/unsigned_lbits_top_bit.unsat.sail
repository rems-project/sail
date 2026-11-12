default Order dec

$include <prelude.sail>

/* The unsigned value of a variable-width bitvector whose top bit is set,
   including one of the maximum width, is not negative. */
$property
function prop(x : bits(8), a : bits(1)) -> bool = {
  let v = 0b1 @ sail_zero_extend(x, 62 + unsigned(a));
  unsigned(v) >= pow2(length(v) - 1)
}
