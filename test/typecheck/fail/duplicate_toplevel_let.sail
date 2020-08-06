default Order dec

$include <prelude.sail>

let X: int = 3
let X: int = 4

function main() -> unit = {
  print_int("X = ", X)
}
