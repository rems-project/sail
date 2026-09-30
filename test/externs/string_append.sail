default Order dec

$include <prelude.sail>
$include <mapping.sail>

// Test for the string_append primitive
function main() -> unit = {
  assert(string_append("foo", "bar") == "foobar");
  assert(string_append("", "bar") == "bar");
  assert(string_append("foo", "") == "foo");
  assert(string_append("", "") == "");
}
