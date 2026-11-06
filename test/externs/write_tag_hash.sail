default Order dec

$sail_internal

$include <prelude.sail>
$include <concurrency_interface/emulator_memory.sail>

// Test for the write_tag# primitive
function main() -> unit = {
  write_tag#(64, 0x0000_0000_0000_1000, true);
  assert(read_tag#(64, 0x0000_0000_0000_1000));
  write_tag#(64, 0x0000_0000_0000_1000, false);
  assert(not_bool(read_tag#(64, 0x0000_0000_0000_1000)));
}
