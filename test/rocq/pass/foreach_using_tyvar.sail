$include <arith.sail>

val f : forall 'n, 'n != 5. int('n) -> unit

val magic : forall 'n. int('n) -> bool effect {rreg}

val g : int -> unit effect {rreg}

function g(x) =
  foreach (n from 0 to x)
    if n != 5 & magic(n) then f(n)
