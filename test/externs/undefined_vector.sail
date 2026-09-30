default Order dec

$include <prelude.sail>

// Test for the undefined_vector primitive
function main() -> unit = {
  let v : vector(4, int) = undefined_vector(4, 0);
  assert(vector_length(v) == 4);
  let w : vector(0, int) = undefined_vector(0, 0);
  assert(vector_length(w) == 0);
}
