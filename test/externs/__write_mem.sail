default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __write_mem primitive
function main() -> unit = {
  assert(__write_mem(Write_plain, 64, 0x0000_0000_0000_1000, 4, 0xDEAD_BEEF));
  assert(__read_mem(Read_plain, 64, 0x0000_0000_0000_1000, 4) == 0xDEAD_BEEF);
}
