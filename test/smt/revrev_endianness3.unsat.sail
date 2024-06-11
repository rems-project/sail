default Order dec

$option -smt_bits_size 128

$include <prelude.sail>
$include <reverse_endianness.sail>

$property
function prop forall 'n, 'n in {8, 16, 32, 64, 128}. (n: int('n), xs: bits(128)) -> bool = {
  let xs = xs[n - 1 .. 0] in
  if length(xs) == 8 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 16 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 32 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 64 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else {
    reverse_endianness(reverse_endianness(xs)) == xs
  }
}
