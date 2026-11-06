default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the string_startswith primitive
function main() -> unit = {
  assert(string_startswith("hello", "he"));
  assert(string_startswith("hello", ""));
  assert(string_startswith("hello", "hello"));
  assert(not_bool(string_startswith("hello", "hello!")));
  assert(not_bool(string_startswith("hello", "el")));
  assert(not_bool(string_startswith("", "a")));
}
