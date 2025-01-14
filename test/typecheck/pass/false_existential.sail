default Order dec
$include <prelude.sail>

/* Careless simplification of the existential type can leave an unused
   'b binding that the type checker rejects. */

val some_bool : unit -> bool

function main() -> unit = {
  let x : {('b : Bool), true. bool('b & false)} = some_bool() & false;
  if x then print_endline("bad") else print_endline("good")
}
