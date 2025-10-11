default Order dec

$include <prelude.sail>

$span start EXAMPLE
register R : bits(64)

function writes_to_R() -> unit = {
  // writing to a register
  R = 0xFFFF_FFFF_FFFF_FFFF;

  R[15 .. 0] = 0x1111;
}

function reads_from_R() -> unit = {
  // reading from a register
  print_bits("the value of the register is ", R)
}
$span end
