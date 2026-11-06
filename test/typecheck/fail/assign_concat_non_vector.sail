default Order dec
$include <prelude.sail>

function f() -> unit = { var x : int = 0; var y : int = 0; (x @ y) = 0b0000 }
