default Order dec

$include <vector_dec.sail>

val main : unit -> unit effect {escape}

function main () = {
  assert(sail_shiftright(0xDEADBEEF, 16) == 0x0000DEAD);
  assert(sail_shiftright(0xDEADBEEF, 4) == 0x0DEADBEE);
  assert(sail_arith_shiftright(0xDEADBEEF, 16) == 0xFFFFDEAD);
  assert(sail_arith_shiftright(0xDEADBEEF, 4) == 0xFDEADBEE);
  assert(sail_shiftleft(0xDEADBEEF, 16) == 0xBEEF0000);
  assert(sail_shiftleft(0xDEADBEEF, 4) == 0xEADBEEF0);
}
