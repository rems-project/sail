
$include <exception_basic.sail>
$include <flow.sail>

val print_endline = "print_endline" : string -> unit

val test : unit -> bool effect {escape}

function test () = {
  assert(false);
  false
}

val main : unit -> unit effect {escape}

function main () = {
  if false & test() then {
    print_endline("unreachable");
  } else {
    print_endline("ok");
  }
}
