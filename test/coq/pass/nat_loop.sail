/* This came up in RISC-V */

default Order dec
$include <prelude.sail>

val f : (bits(32)) -> nat

function f(x) = {
  result : nat = 0;
  foreach (i from 0 to 31)
    if x[i] == bitone then result = result + 1;
  result
}
