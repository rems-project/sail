default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __write_tag primitive
function main() -> unit = {
  assert(__write_tag(Write_plain, 0x0000_0000_0000_1000, bitone));
  let (_, tag) = __read_memt(Read_plain, 0x0000_0000_0000_1000, 1);
  assert(tag == bitone);
}
