default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the extzv primitive
function main() -> unit = {
  let x : bits(8) = extzv(0xF);
  assert(x == 0x0F);
  let y : bits(8) = extzv(0x8F);
  assert(y == 0x8F);
  // Truncates when the result is smaller
  let z : bits(4) = extzv(0xAB);
  assert(z == 0xB);
}
