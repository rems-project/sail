default Order dec

$include <prelude.sail>

register R : bits(8) = 0xF0

register I : int = 20

val main : unit -> unit

function main() = {
  let n = count_trailing_zeros(R);
  print_int("n = ", n);
  let n = count_trailing_zeros(0xF000_0000_0000_0000);
  print_int("n = ", n);

  let len = I;
  let len = if len > 1 then len else 1;
  let zeros = sail_zeros(len);
  let n = count_trailing_zeros(zeros);
  print_int("n = ", n);
}
