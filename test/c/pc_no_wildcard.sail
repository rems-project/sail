default Order dec

$include <prelude.sail>
$include <string.sail>

register R : (bits(1), option(bits(2)))

val test : unit -> int

function test() = {
  match R {
    (_,   Some(0b00)) => 0,
    (0b0, Some(_))    => 1,
    (0b1, _)          => 2,
    (_,   None())     => 3
  }
}

val main : unit -> unit

function main() = {
  R = (0b0, None());
  let x = test();
  print_int("x = ", x)
}
