default Order dec

$include <prelude.sail>

val example1 : unit -> unit

function example1() = {
  let some_value : string = config foo.bar;
  print_endline(some_value);
}
