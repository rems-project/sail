default Order dec
$include <prelude.sail>

struct S = { a : int }
function f(s : S) -> int = s.b
