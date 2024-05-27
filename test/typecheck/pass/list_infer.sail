default Order dec

$include <prelude.sail>

val test : unit -> unit

function test() = {
  let _ = [| 0b00, 0b11 |];
}

val test2 : unit -> unit

function test2() = {
  let _ = [| match 0b00 { x => x }, 0b11 |];
}
