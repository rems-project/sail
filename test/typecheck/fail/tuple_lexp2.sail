default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  var x : int = 0;
  var y : int = 1;
  (x, y) = 2
}
