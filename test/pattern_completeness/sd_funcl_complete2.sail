default Order dec

$include <prelude.sail>

scattered enum e

val foo : e -> unit

enum clause e = A

function clause foo(A) = ()

enum clause e = B

function clause foo(B) = ()

// See sd_funcl_complete1 test, open question of should we require this? Currently no.
end e
