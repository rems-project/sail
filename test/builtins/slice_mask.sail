default Order dec

$include <exception_basic.sail>
$include <flow.sail>
$include <vector_dec.sail>

function main (() : unit) -> unit = {
  assert(slice_mask(32, 8, 4)   == 0x00000F00);
  assert(slice_mask(32, 16, 8)  == 0x00FF0000);
  assert(slice_mask(32, 15, 3)  == 0x00038000);
  assert(slice_mask(32, 16, 32) == 0xFFFF0000);
}
