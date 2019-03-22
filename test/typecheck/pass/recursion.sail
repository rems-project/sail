default Order dec

$include <prelude.sail>

overload operator / = {tdiv_int}

val log2 : int -> int

function log2(n) =
  if n <= 1 then 0 else 1 + log2(n/2)

termination_measure log2(n) = n

val testlog2 : unit -> unit effect {escape}

function testlog2() =
  assert(log2(64) == 6)
