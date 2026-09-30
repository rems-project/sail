default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __read_memt primitive
function main() -> unit = {
  assert(__write_memt(Write_plain, 0x0000_0000_0000_1000, 4, 0xDEAD_BEEF, bitone));
  let (data, tag) = __read_memt(Read_plain, 0x0000_0000_0000_1000, 4);
  assert(data == 0xDEAD_BEEF);
  assert(tag == bitone);
}
