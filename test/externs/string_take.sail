default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the string_take primitive
function main() -> unit = {
  assert(string_take("hello", 0) == "");
  assert(string_take("hello", 2) == "he");
  assert(string_take("hello", 5) == "hello");
  assert(string_take("hello", 10) == "hello");
  assert(string_take("", 3) == "");
}
