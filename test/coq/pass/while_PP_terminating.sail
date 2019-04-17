default Order dec

$include <prelude.sail>

function test n : int -> int = {
  i : int = 1;
  j : int = 1;
  while i < n do {
    j = i * j;
    i = i + 1
  };
  j
}

termination_measure test while n - i
