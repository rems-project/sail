default Order dec

$include <prelude.sail>

// Test for the concat_str primitive
function main() -> unit = {
  assert(concat_str("foo", "bar") == "foobar");
  assert(concat_str("", "bar") == "bar");
  assert(concat_str("foo", "") == "foo");
}
