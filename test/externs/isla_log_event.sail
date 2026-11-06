default Order dec

$include <prelude.sail>
$include <isla.sail>

// Test for the isla_log_event primitive
function main() -> unit = {
  isla_log_event("event", 42);
  isla_log_event("event", 0xAB);
}
