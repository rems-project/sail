default Order dec
$include <prelude.sail>

struct S = { a : int }
function f(x : int) -> unit = match x { struct { a = y } => () }
