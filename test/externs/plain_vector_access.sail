default Order dec

$include <prelude.sail>

// Test for the plain_vector_access primitive
function main() -> unit = {
  // With decreasing order, index 0 is the last element
  let v : vector(3, int) = [1, 2, 3];
  assert(plain_vector_access(v, 0) == 3);
  assert(plain_vector_access(v, 2) == 1);
}
