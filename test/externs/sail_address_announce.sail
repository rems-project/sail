default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the sail_address_announce primitive
function main() -> unit = {
  sail_address_announce(64, 0x0000_0000_8000_0000);
  sail_address_announce(32, 0x8000_0000);
}
