$include <prelude.sail>

/* We currently produce a rich type for the guard of the if that's
   visible in the Coq output.  The raw Sail type involves unbound type
   variables that were existentially bound in x, so in order to print
   out a useful Coq type we now rewrite it in terms of x. */

val isA : unit -> bool effect {rreg}
val isB : unit -> bool effect {rreg}
val isC : unit -> bool effect {rreg}
val foo : bool -> bool effect {rreg}

function foo(b) = {
  let x = (b | isA()) & isB();
  if x | isC() then true else false
}
