default Order dec
$include <prelude.sail>

/* While typing the function call the equations in the type signature may be
   substituted, but substituting *within* these equations was forgotten.
   This was sometimes masked by the order that the instantiation was done (i.e.,
   this example is sensitive to the type variable names). */

val g : forall 'm 'n, 'm == 32 & 'n == div('m, 2). (bits('m), bits('n)) -> unit
val f : (bits(32), bits(16)) -> unit

function f(x,y) = g(x,y)
