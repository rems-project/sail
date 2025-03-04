default Order dec

$include <prelude.sail>

struct S = {
  field : int
}

function main() -> unit = {
  let x : S = struct { field = 3 };
  let x = { x with field = 4, field = 5 };
  print_int("x.field = ", x.field)
}
