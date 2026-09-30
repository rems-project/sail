default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the string_drop primitive
function main() -> unit = {
  assert(string_drop("hello", 0) == "hello");
  assert(string_drop("hello", 2) == "llo");
  assert(string_drop("hello", 5) == "");
  assert(string_drop("hello", 10) == "");
  assert(string_drop("", 3) == "");
}
