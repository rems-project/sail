default Order dec

$include <prelude.sail>
$include <exception_basic.sail>

val main : unit -> unit

function main() = {
  var x : int = 0;

  try {
    x = 1
  } catch {
    Exception() => ()
  };

  print_int("x = ", x)
}
