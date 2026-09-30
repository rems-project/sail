default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __excl_res primitive
function main() -> unit = {
  let b : bool = __excl_res();
  assert(b | not_bool(b));
}
