default Order dec

$include <exception_basic.sail>
$include <flow.sail>
$include <vector_dec.sail>

function main (() : unit) -> unit = {
  v = 0x0BEEF0;
  v[19 .. 4] = 0xDEAD;
  assert(v == 0x0DEAD0, "v == 0x0DEAD0");
  v[0 .. 0] = 0b1;
  assert(v == 0x0DEAD1, "v == 0x0DEAD1");
  v[1 .. 0] = 0b11;
  assert(v == 0x0DEAD3, "v == 0x0DEAD3");
}