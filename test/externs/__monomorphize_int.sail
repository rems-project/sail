default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the __monomorphize_int primitive
function main() -> unit = {
  assert(__monomorphize_int(42) == 42);
  assert(__monomorphize_int(-42) == -42);
}
