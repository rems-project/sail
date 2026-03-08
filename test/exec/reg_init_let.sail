default Order dec
$include <prelude.sail>

let foo = 42
register bar : int = foo

val main : unit -> unit

function main() = {
  print_endline(dec_str(bar))
}
