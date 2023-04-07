default Order dec
$include <prelude.sail>

struct Info('m, 'n) = {
  a: int('m),
  b: bits('n),
}

val f : forall 'm 'n, 'n > 0. (int('m), int('n)) -> Info('m, 'n)
function f(m,n) = struct { a = m, b = sail_zeros(n) }

val run : unit -> unit

function run() = {
  assert(f(3,4).b == sail_zeros(4));
}
