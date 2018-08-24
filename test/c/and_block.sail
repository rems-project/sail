default Order dec

$include <prelude.sail>

val "print" : string -> unit

val main : unit -> unit

function main() = {
  match 432 {
    432 if { (); false } => print("1\n"),
    _ => print("2\n")
  }
}