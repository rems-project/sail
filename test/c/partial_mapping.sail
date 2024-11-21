default Order dec

$include <prelude.sail>

enum Uop = A | B

mapping encdec_uop : Uop <-> bits(5) = {
  A <-> 0b00001,
  B <-> 0b00010
}

union Instr = {
  I1 : Uop,
  I2 : unit
}

$[optimize_control_flow_order]
mapping encdec : Instr <-> bits(8) = {
  I1(op) <-> 0b100 @ encdec_uop(op),
  I2()   <-> 0x00
}

register R : bits(8) = 0b1000_0001

val main : unit -> unit

function main() = {
  let i = encdec(R);
  let _ = encdec(0x00);
  match i {
    I1(A) => print_endline("ok"),
    _ => (),
  }
}
