default Order dec

$include <prelude.sail>

scattered union instr

val encdec : instr <-> bits(32)

scattered mapping encdec

union clause instr = X : bits(21)

mapping clause encdec = X(imm20 @ 0b0)
  <-> 0xF @ imm20[9..0] @ 0x00 @ imm20[19..10]

val main : unit -> unit

function main() = {
  let x = encdec(X(0xFFFFF @ 0b0));
  print_bits("x = ", x);
  let x = encdec(X(0x00000 @ 0b0));
  print_bits("x = ", x);
  let x = encdec(X(0b00 @ 0x00AB @ 0b00 @ 0b0));
  print_bits("x = ", x);

  match encdec(0xFFFC03FF) {
    X(y) => assert(y == 0xFFFFF @ 0b0),
  };

  print_endline("ok");
}