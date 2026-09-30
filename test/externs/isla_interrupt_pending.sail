default Order dec

$include <prelude.sail>
$include <isla.sail>

// Test for the isla_interrupt_pending primitive
function main() -> unit = {
  assert(not_bool(isla_interrupt_pending()));
}
