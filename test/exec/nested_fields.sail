default Order dec

$include <prelude.sail>

struct B = {
  f3: int,
  f4: int,
}

struct A = {
  f1: B,
  f2: int,
}

register R : A

function main() -> unit = {
  R.f1.f3 = 2;
  print_int("", R.f1.f3)
}