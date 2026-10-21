default Order dec
$include <prelude.sail>

union U = { A : (int, int) }
mapping m : U <-> bool = { A(1, 2, 3) <-> true }
