default Order dec

$include <prelude.sail>
$include <smt.sail>

overload operator / = {ediv_int}

union T = {C1 : int, C2 : int}

function test (x : int, y : T) -> int = match y {
  C1(z) if z == 0 => 0,
  C1(z) if z != 0 => x / z,
  C2(z) => z
}
