default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __write_mem_ea primitive
function main() -> unit = {
  __write_mem_ea(Write_plain, 64, 0x0000_0000_0000_1000, 4);
}
