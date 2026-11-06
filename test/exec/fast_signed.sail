default Order dec

$include <prelude.sail>

function main((): unit) -> unit = {
  let x = signed(0xFF);
  let y = signed(0xFFFF);
  let z = signed(0xFFFFFFFF_FFFFFFFF);
  let w = signed(0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF);
  print_int("x = ", x);
  print_int("y = ", y);
  print_int("z = ", z);
  print_int("w = ", w);
  let x = signed(0x80);
  let y = signed(0x8000);
  let z = signed(0x80000000_00000000);
  let w = signed(0x80000000_00000000_00000000_00000000);
  print_int("x = ", x);
  print_int("y = ", y);
  print_int("z = ", z);
  print_int("w = ", w);
  let x = signed(0x7F);
  let y = signed(0x7FFF);
  let z = signed(0x7FFFFFFF_FFFFFFFF);
  let w = signed(0x7FFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF);
  print_int("x = ", x);
  print_int("y = ", y);
  print_int("z = ", z);
  print_int("w = ", w);
}