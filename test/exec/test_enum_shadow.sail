default Order dec

$include <prelude.sail>

enum E = {A, B, C, D}

register R : E

val f : E -> int

function f(x) = {
  match R {
    A => match x {
      B => 2,
      A => 1,
      D => 4,
      C => 3,
    },
    _ => 999,
  }
}

val main : unit -> unit

function main() = {
  R = A;
  print_int("A = ", f(A));
  print_int("B = ", f(B));
  print_int("C = ", f(C));
  print_int("D = ", f(D));
}
