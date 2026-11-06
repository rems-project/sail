default Order dec
$include <prelude.sail>

union U = { A : int, B : bool }
$[undefined_gen "generate"]
struct S = { a : U }
