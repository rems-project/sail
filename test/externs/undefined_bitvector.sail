default Order dec

$include <prelude.sail>

// Test for the undefined_bitvector primitive
function main() -> unit = {
  let v : bits(8) = undefined_bitvector(8);
  assert(bitvector_length(v) == 8);
  let w : bits(100) = undefined_bitvector(100);
  assert(bitvector_length(w) == 100);
}
