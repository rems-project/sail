default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the extsv primitive
function main() -> unit = {
  let x : bits(8) = extsv(0xF);
  assert(x == 0xFF);
  let y : bits(8) = extsv(0x7);
  assert(y == 0x07);
  // Truncates when the result is smaller
  let z : bits(4) = extsv(0xAB);
  assert(z == 0xB);
}
