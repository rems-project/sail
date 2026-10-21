default Order dec

$include <prelude.sail>

// Test for the vector_init primitive
function main() -> unit = {
  let v : vector(3, int) = vector_init(7);
  assert(vector_length(v) == 3);
  assert(v[0] == 7);
  assert(v[2] == 7);
}
