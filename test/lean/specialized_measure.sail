default Order dec
$include <prelude.sail>
$option -const_prop_mutrec outer

val outer : nat -> bool
val inner : (bool, nat) -> bool
termination_measure outer(n) = n + 1
termination_measure inner(_, n) = n

function outer(n) = inner(false, n)
function inner(recur, n) = if recur & n > 0 then outer(n - 1) else true
