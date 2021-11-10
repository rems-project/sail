default Order dec

$include <exception_basic.sail>
$include <flow.sail>
$include <vector_dec.sail>

function main (() : unit) -> unit = {
  v = 0x0BEEF0;
  v[0] = bitone;
  assert(v == 0x0BEEF1, "v == 0x0BEEF1");
  v[1] = bitone;
  assert(v == 0x0BEEF3, "v == 0x0BEEF3");
  v[4] = bitzero;
  assert(v == 0x0BEEE3, "v == 0x0BEEE3");
}
