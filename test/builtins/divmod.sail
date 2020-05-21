default Order dec

$include <exception_basic.sail>
$include <arith.sail>
$include <smt.sail>

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

  assert(fdiv_int(5, 2) == 2);
  assert(fdiv_int(-5, -2) == 2);
  assert(fdiv_int(5, -2) == -3);
  assert(fdiv_int(-5, 2) == -3);

  assert(tdiv_int(5, 2) == 2);
  assert(tdiv_int(-5, -2) == 2);
  assert(tdiv_int(5, -2) == -2);
  assert(tdiv_int(-5, 2) == -2);
}