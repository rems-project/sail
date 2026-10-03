default Order dec

$include <prelude.sail>

struct S = {
  f1 : int,
  f2 : int,
}

function foo(struct { f1, _ } : S, x : nat) -> unit = {
  print_int("f1 = ", f1);
}

function main() -> unit = {
  foo(struct { f1 = 3, f2 = 4 }, 5);
}
