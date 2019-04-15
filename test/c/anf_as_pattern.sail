default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

function test () : unit -> option(int) = {
  match Some(3) {
    Some(_) as x => x,
    _ => None()
  }
}

function main() : unit -> unit = {
  match test() {
    Some(3) => print_endline("ok"),
    _ => print_endline("fail")
  }
}