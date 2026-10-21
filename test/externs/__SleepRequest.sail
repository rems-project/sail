default Order dec

$include <prelude.sail>
$include <asl_compat.sail>

// Test for the __SleepRequest primitive
function main() -> unit = {
  __SleepRequest();
}
