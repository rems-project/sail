default Order dec
$include <prelude.sail>

// Use the dumped AST recheck to ensure that val-specs and val-specs generated
// from function annotations are expanded in the same way.

val f : unit -> bits(8)
function f() = sail_zeros(8)

function g() -> bits(8) = sail_zeros(8)
