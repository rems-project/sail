default Order dec

$include <prelude.sail>

struct pair = {
    lhs: int,
    rhs: int,
}

val test : pair <-> (int, int)

mapping test = {
  struct { lhs = x, rhs = y } <-> (x, y)
}

val main : unit -> unit

function main() = {
  let struct { lhs = x, rhs = y } = test((1, 3));
  print_int("x = ", x);
  print_int("y = ", y);

  let (x, y) = test(struct { lhs = 2, rhs = 4 });
  print_int("x = ", x);
  print_int("y = ", y)
}
