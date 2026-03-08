default Order dec

$include <arith.sail>
$include <smt.sail>
$include <string.sail>

function main (() : unit) -> unit = {
  assert(ediv_int(7, 5) == 1);
  assert(ediv_int(7, -5) == -1);
  assert(ediv_int(-7, 5) == -2);
  assert(ediv_int(-7, -5) == 2);
  assert(ediv_int(12, 3) == 4);
  assert(ediv_int(12, -3) == -4);
  assert(ediv_int(-12, 3) == -4);
  assert(ediv_int(-12, -3) == 4);

  assert(emod_int(7, 5) == 2);
  assert(emod_int(7, -5) == 2);
  assert(emod_int(-7, 5) == 3);
  assert(emod_int(-7, -5) == 3);
  assert(emod_int(12, 3) == 0);
  assert(emod_int(12, -3) == 0);
  assert(emod_int(-12, 3) == 0);
  assert(emod_int(-12, -3) == 0);

  print_endline("ediv ok")
}
