default Order dec

$include <prelude.sail>

val pair : (bits(8), bits(8)) -> (bits(8), bits(8))
function pair(a, b) = (b, a)

/* A tuple assignment to local variables: each must keep its new value. */
val swap_first : (bits(8), bits(8)) -> bits(8)
function swap_first(x, y) = {
  var r : bits(8) = 0x00;
  var s : bits(8) = 0x00;
  (r, s) = pair(x, y);
  r
}

/* The same, and both variables read afterwards. */
val swap_both : (bits(8), bits(8)) -> bits(16)
function swap_both(x, y) = {
  var r : bits(8) = 0x00;
  var s : bits(8) = 0x00;
  (r, s) = pair(x, y);
  r @ s
}

function main() -> unit = {
  print_bits("first = ", swap_first(0x12, 0x34));
  print_bits("both = ", swap_both(0x12, 0x34))
}
