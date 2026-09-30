default Order dec

$include <prelude.sail>

// Test for the plain_vector_update primitive
function main() -> unit = {
  let v : vector(3, int) = [1, 2, 3];
  let w = plain_vector_update(v, 0, 7);
  assert(plain_vector_access(w, 0) == 7);
  assert(plain_vector_access(w, 1) == 2);
  assert(plain_vector_access(w, 2) == 1);
  // The original vector is unchanged
  assert(plain_vector_access(v, 0) == 3);
}
