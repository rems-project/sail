val f : (atom(10), unit) -> atom(10)

function f (x, y) = x

val test : unit -> atom(10)

function test () = {
  z = 10;
  z
}

val test2 : unit -> unit

function test2 () = x = 10
