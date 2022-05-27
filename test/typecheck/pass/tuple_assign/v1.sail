default Order dec
$include <prelude.sail>

val some_tuple = monadic "some_tuple" : unit -> (int, int, int)

val all_updated : unit -> int

function all_updated() = {
  x : int = 0;
  y : int = 0;
  z : int = 0;
  (x,y,z) = some_tuple();
  x + y + z
}

val all_declared : unit -> int

function all_declared() = {
  (x,y,z) = some_tuple();
  x + y + z
}

/* Mixing updates and implicit declarations is not allowed */
val bad_mixed : unit -> int

function bad_mixed() = {
  x : int = 0;
  z : int = 0;
  (x,y,z) = some_tuple();
  x + y + z
}

