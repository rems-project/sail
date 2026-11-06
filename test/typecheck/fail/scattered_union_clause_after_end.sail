default Order dec

$include <prelude.sail>

scattered union U
union clause U = A : int
end U

function f(x : U) -> int = match x { A(n) => n }

union clause U = B : int
