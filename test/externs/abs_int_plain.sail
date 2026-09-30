default Order dec

$include <prelude.sail>

// Test for the abs_int_plain primitive
function main() -> unit = {
  let x : int = -5;
  assert(abs_int_plain(x) == 5);
  assert(abs_int_plain(5) == 5);
  assert(abs_int_plain(0) == 0);
  assert(abs_int_plain(-18446744073709551616) == 18446744073709551616);
}
