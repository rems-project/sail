default Order dec
$include <prelude.sail>

/* If a definition is shadowed by an external declaration, then we shouldn't add effects to deal
   with the loops in the definition. */

val mypow2 = pure { coq: "pow2" } : int -> int

function mypow2(i) = if i <= 0 then 1 else 2 * mypow2(i - 1)

termination_measure mypow2(i) = i

function main() -> int = {
  let n = mypow2(10);
  n + 1
}
