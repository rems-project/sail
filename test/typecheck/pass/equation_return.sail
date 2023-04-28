default Order dec
$include <prelude.sail>

// When applying foo, the unification of 8 * 'n and 64 provides the
// value for 'n.  For bar, that must come from the equation.

val foo : forall 'n, 'n >= 0. implicit('n) -> bits(8 * 'n)
val bar : forall 'n 'm, 'n >= 0 & 'm == 8 * 'n. implicit('n) -> bits('m)

val f : unit -> unit

function f() = {
  let w: bits(64) = foo();
  let v: bits(64) = bar();
  ()
}
