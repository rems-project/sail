default Order dec
$include <prelude.sail>

function main () : unit -> unit = {
  assert(count_trailing_zeros(0x0) == 4);
  assert(count_trailing_zeros(0x1) == 0);
  assert(count_trailing_zeros(0x4) == 2);
  assert(count_trailing_zeros(0xf) == 0);

  foreach (i from 0 to 32 by 1 in inc) {
    assert(count_trailing_zeros(sail_shiftleft(0x00000001, i)) == i);
  }
}
