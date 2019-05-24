default Order dec
$include <prelude.sail>

union exception = {
  BadInput : int
}

val test1 : int -> nat effect {escape}

function test1(n) = {
  if (n < 0) then {
    throw (BadInput(n))
  };
  n
}

val test2 : int -> nat effect {escape}

function test2(n) = {
  m : nat = 0;
  if (n < 0) then {
    throw (BadInput(n))
  } else { m = 1 };
  n+m
}
