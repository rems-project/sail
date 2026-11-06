default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  match true {
    _ => print_endline("ok"),
    _ => print_endline("fail"),
  }
}
