default Order dec

$include <prelude.sail>

$option -abstract_types

type b : Bool

val some_int : unit -> int

val only_true : bool(true) -> unit

val test : bool(b) -> unit

function test(b) = {
  let x = b;
  let y = some_int();
  if x | y == 32 then {
    if y != 32 then {
      only_true(x)
    }
  }
}
