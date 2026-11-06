default Order dec

$sail_internal

$include <prelude.sail>
$include <concurrency_interface/emulator_memory.sail>

// Test for the write_mem# primitive
function main() -> unit = {
  assert(write_mem#((), 64, 0x0000_0000_0000_1000, 8, 0x0123_4567_89AB_CDEF));
  assert(read_mem#((), 64, 0x0000_0000_0000_1000, 8) == 0x0123_4567_89AB_CDEF);
  // Memory is little-endian
  assert(write_mem#((), 64, 0x0000_0000_0000_1000, 1, 0xFF));
  assert(read_mem#((), 64, 0x0000_0000_0000_1000, 8) == 0x0123_4567_89AB_CDFF);
  assert(write_mem#((), 32, 0x0000_2000, 2, 0xCAFE));
  assert(read_mem#((), 32, 0x0000_2000, 2) == 0xCAFE);
}
