default Order dec

$include <arith.sail>
$include <string.sail>

function main (() : unit) -> unit = {
  assert(fdiv_int(7, 5) == 1);
  assert(fdiv_int(7, -5) == -2);
  assert(fdiv_int(-7, 5) == -2);
  assert(fdiv_int(-7, -5) == 1);
  assert(fdiv_int(12, 3) == 4);
  assert(fdiv_int(12, -3) == -4);
  assert(fdiv_int(-12, 3) == -4);
  assert(fdiv_int(-12, -3) == 4);

  assert(fmod_int(7, 5) == 2);
  assert(fmod_int(7, -5) == -3);
  assert(fmod_int(-7, 5) == 3);
  assert(fmod_int(-7, -5) == -2);
  assert(fmod_int(12, 3) == 0);
  assert(fmod_int(12, -3) == 0);
  assert(fmod_int(-12, 3) == 0);
  assert(fmod_int(-12, -3) == 0);

  print_endline("fdiv ok")
}
