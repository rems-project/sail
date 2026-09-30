default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the string_length primitive
function main() -> unit = {
  assert(string_length("") == 0);
  assert(string_length("a") == 1);
  assert(string_length("hello") == 5);
}
