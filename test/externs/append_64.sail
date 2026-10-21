default Order dec

$include <prelude.sail>

// Test for the append_64 primitive
function main() -> unit = {
  assert(append_64(0xF, 0x0123_4567_89AB_CDEF) == 0xF_0123_4567_89AB_CDEF);
  assert(append_64(sail_zeros(0), 0x0123_4567_89AB_CDEF) == 0x0123_4567_89AB_CDEF);
}
