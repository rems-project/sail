default Order dec
$include <prelude.sail>

val zero_int_bits : forall 'm, 'm >= 0. int('m) <-> bits('m)
function zero_int_bits_forwards_matches(_) = true
function zero_int_bits_forwards(m) = sail_zeros(m)
function zero_int_bits_backwards_matches(v) = (v == sail_zeros(length(v)))
function zero_int_bits_backwards(v) = length(v)

val test1 : unit -> unit
function test1() =
{
  print_bits("zero_int_bits_forwards ", zero_int_bits(32));
  print_int("zero_int_bits_backwards ", zero_int_bits(0b0000))
}

mapping test1m : bits(3) <-> bits(5) = { v <-> zero_int_bits(2) @ v }

mapping test2m : bits(3) <-> bits(5) = { v <-> zero_int_bits(2) : bits(2) @ v }

val main : unit -> unit

function main() = {
  test1();
  print_bits("test1m ", test1m(0b111));
  print_bits("test1m ", test1m(0b00111));
  print_bits("test2m ", test1m(0b111));
  print_bits("test2m ", test1m(0b00111));
}
