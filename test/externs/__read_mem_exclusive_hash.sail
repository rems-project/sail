default Order dec

$sail_internal

$include <prelude.sail>
$include <concurrency_interface/emulator_memory.sail>

// Test for the __read_mem_exclusive# primitive
function main() -> unit = {
  assert(__write_mem#(64, 0x0000_0000_0000_1000, 4, 0xDEAD_BEEF));
  assert(__read_mem_exclusive#(64, 0x0000_0000_0000_1000, 4) == 0xDEAD_BEEF);
  // Memory is little-endian
  assert(__read_mem_exclusive#(64, 0x0000_0000_0000_1000, 1) == 0xEF);
  assert(__read_mem_exclusive#(64, 0x0000_0000_0000_1003, 1) == 0xDE);
  assert(__read_mem_exclusive#(64, 0x0000_0000_0000_1001, 2) == 0xADBE);
  assert(__write_mem#(32, 0x0000_2000, 2, 0xCAFE));
  assert(__read_mem_exclusive#(32, 0x0000_2000, 2) == 0xCAFE);
}
