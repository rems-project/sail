default Order dec
$include <prelude.sail>

register R : bits(4)
register C : bool

struct S = { a : bits(4), b : bits(4) }

/* An effectful conditional assigned to a field: in the Lean output it follows `field := ←`, so
   the nested register reads in its branches need a do block of their own. */
val f : S -> S
function f(s0) = {
  var s = s0;
  s.a = if C then not_vec(R) else 0x0;
  s.b = match C { true => not_vec(R), false => R };
  s
}
