default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  var once : bool = false;
  repeat {
    print_endline("Once");
    once = true;
  } until once;
}
