default Order dec
$include <prelude.sail>

overload operator / = {tdiv_int}

function log2_while(n : int) -> int = {
  var m : int = n;
  var r : int = 0;
  while m > 1 {
    r = r + 1;
    m = m / 2;
  };
  r
}

termination measure log2_while while (n)

function log2_recursive(n : int) -> int =
  if n <= 1 then 0 else 1 + log2_recursive(n/2)

termination_measure log2_recursive(n) = n

val testlog2 : unit -> unit effect {escape}

function testlog2() = {
  assert(log2_while(64) == 6);
  assert(log2_recursive(64) == 6)
}
