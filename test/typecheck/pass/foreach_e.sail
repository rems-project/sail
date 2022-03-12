default Order dec

$include <prelude.sail>

val test : unit -> int

function test() = {
  foreach (i from 1 to 4) {
    if i == 2 then {
      return i + 5
    }
  };
  0
}

let x = test()
