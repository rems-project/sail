default Order dec
$include <prelude.sail>

function main () : unit -> unit = {
  assert(count_leading_zeros(0x0) == 4);
  assert(count_leading_zeros(0x1) == 3);
  assert(count_leading_zeros(0x4) == 1);
  assert(count_leading_zeros(0xf) == 0);
}