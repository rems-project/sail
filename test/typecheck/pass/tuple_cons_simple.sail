default Order dec
$include <prelude.sail>

/* The remove_e_assign rewrite was lifting out the subexpressions from the tuple,
   but failing to include enough typing information.  This simple case ought to
   be left alone.

   Note that this test is really for the Rocq and Lem backends; plain type
   checking should be straightforward.
   */

function test(xs : list(int), ys : list(int)) -> (list(int), list(int)) =
  (5 :: xs, 3 :: ys)
