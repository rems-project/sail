default Order dec

$include <prelude.sail>

function get_16((): unit) -> range(0, 16) = 16
function get_8((): unit) -> range(0, 16) = 8

function main((): unit) -> unit = {
  let x = get_16();
  let y = get_8();
  let addr = 0x1234_ABCD;
  let v1 = slice(addr, 16, x);
  let v2 = slice(addr, 16, y);
  print_bits("v1 = ", v1);
  print_bits("v2 = ", v2);
}