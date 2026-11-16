default Order dec
$include <prelude.sail>

// We used to skip a do at the assignment despite the register read

register R1 : bits(32)

function f(b : bool, x : int) -> bits(32) = {
  var y : bits(32) = 0x00000000;
  y : bits(32) = if b then R1 else R1 - x;
  y + 0x00000000
}
