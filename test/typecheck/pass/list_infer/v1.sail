default Order dec

$include <prelude.sail>

val test : unit -> unit

function test() = {
  let _ = [| 0b00, 0b11, 0b111 |];
}
