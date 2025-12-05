default Order dec
$include <prelude.sail>

union foo = {
  A : bits(32),
  B : int,
}

val f : foo -> bool

/* The guarded patterns rewrite will need to substitute for v for w when merging below,
   check that it works. */

function f (A(v) if v == 0x00000000) = true
and f (A(w) if w != 0x00000000) = false
and f _ = false
