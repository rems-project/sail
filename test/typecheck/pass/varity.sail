val f1 : int -> unit

val f2 : (int, int) -> unit

val f3 : (int, int, int) -> unit

function f1 i1 = ()

function f2 (i1, i2) = ()

function f3 (i1, i2, i3) = ()

overload f = {f1, f2, f3}

val test : unit -> unit

function test () = {
  f(1);
  f(2, 3);
  f(4, 5, 6)
}
