default Order dec

$include <prelude.sail>
$include <asl_compat.sail>

// Test for the __WakeupRequest primitive
function main() -> unit = {
  __WakeupRequest();
}
