default Order dec

$include <exception_basic.sail>
$include <flow.sail>
$include <vector_dec.sail>
$include <arith.sail>

function main (() : unit) -> unit = {
  assert(shl_int(1, 10) == 1024);
  assert(shl_int(1, 2) == 4);
  assert(shl_int(1, 3) == 8);
  assert(shl_int(1, 4) == 16);
  assert(shl_int(1, 5) == 32);
  assert(shl_int(1, 6) == 64);
  assert(shl_int(8, 0) == 8);
  assert(shl_int(8, 2) == 32);
  assert(shl_int(8, 3) == 64);

  assert(shl_int(1024, -10) == 1);
  assert(shl_int(4,     -2) == 1);
  assert(shl_int(8,     -3) == 1);
  assert(shl_int(16,    -4) == 1);
  assert(shl_int(32,    -5) == 1);
  assert(shl_int(64,    -6) == 1);
  assert(shl_int(8,     -0) == 8);
  assert(shl_int(32,    -2) == 8);
  assert(shl_int(64,    -3) == 8);
}
