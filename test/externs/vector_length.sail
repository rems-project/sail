default Order dec

$include <prelude.sail>

// Test for the vector_length primitive
function main() -> unit = {
  let v : vector(3, int) = [1, 2, 3];
  assert(vector_length(v) == 3);
  let w : vector(1, string) = ["a"];
  assert(vector_length(w) == 1);
}
