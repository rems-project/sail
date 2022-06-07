default Order dec
$include <prelude.sail>

val f : forall 'n, 'n in {16, 32}. bits('n) -> bits('n)

function f(v) = {
  result : bits('n) = undefined;
  if [v['n - 1]] == 0b0 then {
    result = sail_zeros('n)
  } else {
    result = 0x5 @ sail_zeros('n - 4)
  };
  return(result)
}

val g : forall 'n, 'n in {16, 32}. (implicit('n), bits('n)) -> bits('n)

function g(n, v) = {
  result : bits('n) = undefined;
  if [v[n - 1]] == 0b0 then {
    result = sail_zeros(n)
  } else {
    result = 0x5 @ sail_zeros(n - 4)
  };
  return(result)
}

val run : unit -> unit

function run() = {
  assert(f(0x0000) == 0x0000);
  assert(f(0x8000) == 0x5000);
  assert(f(0x00000000) == 0x00000000);
  assert(f(0x00008000) == 0x00000000);
  assert(f(0x80000000) == 0x50000000);
  assert(g(0x0000) == 0x0000);
  assert(g(0x8000) == 0x5000);
  assert(g(0x00000000) == 0x00000000);
  assert(g(0x00008000) == 0x00000000);
  assert(g(0x80000000) == 0x50000000);
}
