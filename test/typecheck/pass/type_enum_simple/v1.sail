default Order dec

$include <prelude.sail>

enum my_enum = A | B | C

enum my_enum2 = D | E

val h : {A, D} -> unit

val main : unit -> unit

function main() = {
  _not_check(h(C) : unit);
  h(A);
  h(B)
}
