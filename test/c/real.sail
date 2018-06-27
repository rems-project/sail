
$include <arith.sail>
$include <real.sail>

val main : unit -> unit

function main() = {
  let x : real = 16.0;
  print_real("1: ", x);
  print_int("1: ", floor(x));
  print_int("1: ", ceil(x));
  print_real("1: ", sqrt(x));
  print_int("1: ", floor(sqrt(x)));
  print_int("1: ", ceil(sqrt(x)));
  let x : real = 17.0;
  print_real("2: ", x);
  print_int("2: ", floor(x));
  print_int("2: ", ceil(x));
  print_real("2: ", sqrt(x));
  print_int("2: ", floor(sqrt(x)));
  print_int("2: ", ceil(sqrt(x)));
}