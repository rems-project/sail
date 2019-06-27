default Order dec

$include <reverse_endianness.sail>

$property
function prop forall 'n, 'n in {8, 16, 32, 64, 128}. (n: int('n), xs: bits('n)) -> bool = {
  if length(xs) == 8 then {
    let ys: bits(8) = xs;
    reverse_endianness(reverse_endianness(ys)) == ys
  } else if length(xs) == 16 then {
    let ys: bits(16) = xs;
    reverse_endianness(reverse_endianness(ys)) == ys
  } else if length(xs) == 32 then {
    let ys: bits(32) = xs;
    reverse_endianness(reverse_endianness(ys)) == ys
  } else if length(xs) == 64 then {
    let ys: bits(64) = xs;
    reverse_endianness(reverse_endianness(ys)) == ys
  } else if length(xs) == 128 then {
    let ys: bits(128) = xs;
    reverse_endianness(reverse_endianness(ys)) == ys
  } else {
    true
  }
}
