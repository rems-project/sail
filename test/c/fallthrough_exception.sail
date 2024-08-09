default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

union exception = {
  E1 : unit,
  E2 : unit
}

function main((): unit) -> unit = {
  try {
    try throw(E2()) catch {
      E1() => print_endline("E1")
    }
  } catch {
    E2() => print_endline("E2")
  }
}
