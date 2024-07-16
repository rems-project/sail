default Order dec

$include <prelude.sail>

enum my_enum = A | B | C

val h : {A, B} -> unit

val main : unit -> unit

function main() = {
  _not_check(h(C) : unit);
  h(A);
  h(B)
}
