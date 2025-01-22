default Order dec

$include <prelude.sail>

val example : unit -> unit

function example() = {
  let n : {32, 64} = config some.integer;
}
