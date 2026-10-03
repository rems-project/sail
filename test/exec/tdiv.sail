default Order dec

$include <arith.sail>
$include <string.sail>

function main (() : unit) -> unit = {
  assert(tdiv_int(7, 5) == 1);
  assert(tdiv_int(7, -5) == -1);
  assert(tdiv_int(-7, 5) == -1);
  assert(tdiv_int(-7, -5) == 1);
  assert(tdiv_int(12, 3) == 4);
  assert(tdiv_int(12, -3) == -4);
  assert(tdiv_int(-12, 3) == -4);
  assert(tdiv_int(-12, -3) == 4);

  assert(tmod_int(7, 5) == 2);
  assert(tmod_int(7, -5) == 2);
  assert(tmod_int(-7, 5) == -2);
  assert(tmod_int(-7, -5) == -2);
  assert(tmod_int(12, 3) == 0);
  assert(tmod_int(12, -3) == 0);
  assert(tmod_int(-12, 3) == 0);
  assert(tmod_int(-12, -3) == 0);

  print_endline("tdiv ok")
}
