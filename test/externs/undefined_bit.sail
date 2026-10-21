default Order dec

$include <prelude.sail>

// Test for the undefined_bit primitive
function main() -> unit = {
  let b : bit = undefined_bit();
  assert(b == bitzero | b == bitone);
}
