default Order dec

$include <prelude.sail>
$include <isla.sail>

register R : bits(32) = 0x0000_0000
register S : bits(64) = 0x0000_0000_0000_0000

// Test for the isla_synchronize_registers primitive
function main() -> unit = {
  R = 0xDEAD_BEEF;
  isla_synchronize_registers();
  assert(R == 0xDEAD_BEEF);
}
