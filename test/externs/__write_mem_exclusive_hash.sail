default Order dec

$sail_internal

$include <prelude.sail>
$include <concurrency_interface/emulator_memory.sail>

// Test for the __write_mem_exclusive# primitive
function main() -> unit = {
  assert(__write_mem_exclusive#(64, 0x0000_0000_0000_1000, 8, 0x0123_4567_89AB_CDEF));
  assert(__read_mem#(64, 0x0000_0000_0000_1000, 8) == 0x0123_4567_89AB_CDEF);
  // Memory is little-endian
  assert(__write_mem_exclusive#(64, 0x0000_0000_0000_1000, 1, 0xFF));
  assert(__read_mem#(64, 0x0000_0000_0000_1000, 8) == 0x0123_4567_89AB_CDFF);
  assert(__write_mem_exclusive#(32, 0x0000_2000, 2, 0xCAFE));
  assert(__read_mem#(32, 0x0000_2000, 2) == 0xCAFE);
}
