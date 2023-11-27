default Order dec

$include <prelude.sail>

$span start TUPLES
let tuple1 : (string, int) = ("Hello, World!", 3)

let tuple2 : (nat, nat, nat) = (1, 2, 3)
$span end

val single_tuple_argument : ((int, int)) -> unit

function single_tuple_argument(tuple) = {
  let (x, y) = tuple;
  print_int("x = ", x);
  print_int("y = ", y);
}

function caller() -> unit = {
  single_tuple_argument((1, 2))
}