default Order dec

$include <prelude.sail>

val foo : unit -> {1, 2, 3}

function bar() -> unit = {
  match foo() {
    1 => (),
    2 => (),
    3 => (),
  }
}
