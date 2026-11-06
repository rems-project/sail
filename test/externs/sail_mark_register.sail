default Order dec

$include <prelude.sail>
$include <concurrency_interface.sail>

register R : bits(32) = 0x0000_0000
register S : bits(64) = 0x0000_0000_0000_0000

// Test for the sail_mark_register primitive
function main() -> unit = {
  sail_mark_register(ref R, "test");
  R = 0xDEAD_BEEF;
  assert(R == 0xDEAD_BEEF);
}
