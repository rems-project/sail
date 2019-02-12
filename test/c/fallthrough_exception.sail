default Order dec

$include <prelude.sail>

val print = "print_endline" : string -> unit

union exception = {
  E1 : unit,
  E2 : unit
}

function main((): unit) -> unit = {
  try {
    try throw(E2()) catch {
      E1() => print("E1")
    }
  } catch {
    E2() => print("E2")
  }
}