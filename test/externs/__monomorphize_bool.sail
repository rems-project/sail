default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the __monomorphize_bool primitive
function main() -> unit = {
  assert(__monomorphize_bool(true));
  assert(not_bool(__monomorphize_bool(false)));
}
