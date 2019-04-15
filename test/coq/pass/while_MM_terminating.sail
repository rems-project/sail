default Order dec

$include <prelude.sail>

register COUNT : int

register INT : bool

function test () -> unit = {
  COUNT = 0;
  while not_bool(INT) do {
    COUNT = COUNT + 1;
    if COUNT > 5 then
      INT = true
  }
}

termination_measure test while (5 - COUNT)
