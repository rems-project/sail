default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  var foo = 3;
  (foo, bar) = (2, 4);
  ()
}