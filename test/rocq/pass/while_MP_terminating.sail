default Order dec

$include <prelude.sail>

register INT : bool

function test () -> int = {
  count : int = 0;
  while not_bool(INT) & count < 5 do count = count + 1;
  return(count)
}

termination_measure test while 5 - count
