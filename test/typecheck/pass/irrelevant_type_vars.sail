default Order dec
$include <prelude.sail>

/* These awkward types can be produced during rewriting, especially when the code is put into monadic form and some
   variables are fixed by external configuration.  When Sail simplifies these they should just end up as bool(false)
   instead of an existential. */

function f(n : nat) -> bool = {
  let b : {'n, 'n >= 0. bool('n < 5 & false)} = n < 5 & false;
  b
}
