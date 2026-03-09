default Order dec
$include <prelude.sail>

/* Currently we don't simplify larger powers of two in types.  Check that we can cope with that in
   the Rocq output. */

register r0 : bits(2 ^ 17)
