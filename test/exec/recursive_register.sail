default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>
$include <string.sail>

register R : int

val cond : unit -> bool

function cond() = {
  R = R + 1;
  R < 3
}

val loop : unit -> unit
function loop() =
  if cond() then loop() else ()

val main : unit -> unit

function main() =
{
  R = 0;
  loop();
  print_int("R = ", R);
}
