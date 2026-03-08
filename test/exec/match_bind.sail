default Order dec

$include <prelude.sail>

function main() -> unit = {
  let x: int = 3;
  match x {
    _ if let y = x in y == 3 => let y = x in print_int("1. y = ", y),
    _ if let y = x in true => let y = x in print_int("2. y = ", y)
  }
}