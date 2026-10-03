default Order dec
$include <prelude.sail>

function f(b : bool) -> unit = { let x = if b then 1 else "a"; () }
