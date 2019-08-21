$option -dmagic_hash

default Order dec

$include <prelude.sail>
$include <mapping.sail>

enum E = A | B | C

mapping test : E <-> range(1, 3) = {
  A <-> 1,
  B <-> 2,
  C <-> 3
}

function main() -> unit = {
  match A {
    x <- test() if x == 1, if x != 2 => print_int("view", x)
  }
}