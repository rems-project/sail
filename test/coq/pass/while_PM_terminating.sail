default Order dec

$include <prelude.sail>

register GPR00 : int

function test b : int -> unit = {
  i : int = 0;
  while i < 64 do {
    GPR00 = b + i;
    i = i + 1;
  }
}

termination_measure test while 64 - i
