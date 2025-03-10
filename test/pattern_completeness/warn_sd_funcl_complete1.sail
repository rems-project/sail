default Order dec

$include <prelude.sail>

scattered enum e

val foo : e -> unit

enum clause e = A

function clause foo(A) = ()

enum clause e = B

function clause foo(B) = ()

enum clause e = C

function main() -> unit = {
  foo(C)
}
