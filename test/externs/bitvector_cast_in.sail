default Order dec

$include <prelude.sail>
$include <mono_rewrites.sail>

// Test for the bitvector_cast_in primitive
function main() -> unit = {
  assert(bitvector_cast_in(0xAB) == 0xAB);
  assert(bitvector_cast_in(0b1) == 0b1);
}
