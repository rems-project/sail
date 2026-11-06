default Order dec

$include <prelude.sail>

union exception = {
  E_string : string
}

val f : unit -> unit

$[jib_debug]
function f() = throw E_string("Hello, World!")

val main : unit -> unit

function main() = {
  try f() catch {
    E_string(msg) => print_endline(msg)
  }
}
