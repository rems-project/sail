default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

// Test for the sail_instr_announce primitive
function main() -> unit = {
  sail_instr_announce(0xDEAD_BEEF);
  sail_instr_announce(0b1);
}
