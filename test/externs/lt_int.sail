default Order dec

$include <prelude.sail>

// Test for the lt_int primitive
function main() -> unit = {
  assert(lt_int(3, 5));
  assert(not_bool(lt_int(5, 5)));
  assert(not_bool(lt_int(6, 5)));
  assert(lt_int(-18446744073709551616, 18446744073709551616));
}
