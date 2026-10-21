default Order dec

$include <prelude.sail>
$include <smt.sail>

type test_div : Int = div(-3, -2)

bitfield b : bits(test_div) = {
  F : 1 .. 0
}

register R : b

val main : unit -> unit

function main() = {
  _prove(constraint(div(-3, -2) == 2));
  let 'len = length(R.bits);
  _prove(constraint('len == 2));
  assert(ediv_int(-3, -2) == 2);
  assert(tdiv_int(-3, -2) == 1);
  assert(fdiv_int(-3, -2) == 1);
  print_endline("ok");
}
