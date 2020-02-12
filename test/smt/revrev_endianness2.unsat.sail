default Order dec

$include <reverse_endianness.sail>

$property
function prop forall 'n, 'n in {8, 16, 32, 64, 128}. (n: int('n), xs: bits('n)) -> bool = {
  if length(xs) == 8 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 16 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 32 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 64 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else if length(xs) == 128 then {
    reverse_endianness(reverse_endianness(xs)) == xs
  } else {
    true
  }
}
