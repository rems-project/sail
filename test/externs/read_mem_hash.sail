default Order dec

$sail_internal

$include <prelude.sail>
$include <concurrency_interface/emulator_memory.sail>

// Test for the read_mem# primitive
function main() -> unit = {
  assert(write_mem#((), 64, 0x0000_0000_0000_1000, 4, 0xDEAD_BEEF));
  assert(read_mem#((), 64, 0x0000_0000_0000_1000, 4) == 0xDEAD_BEEF);
  // Memory is little-endian
  assert(read_mem#((), 64, 0x0000_0000_0000_1000, 1) == 0xEF);
  assert(read_mem#((), 64, 0x0000_0000_0000_1003, 1) == 0xDE);
  assert(read_mem#((), 64, 0x0000_0000_0000_1001, 2) == 0xADBE);
  assert(write_mem#((), 32, 0x0000_2000, 2, 0xCAFE));
  assert(read_mem#((), 32, 0x0000_2000, 2) == 0xCAFE);
}
