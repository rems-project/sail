$include <prelude.sail>

val f : forall 'n, 'n in {8,16}. atom('n) -> atom('n)

val make : unit -> {'n, 'n in {8,16}. atom('n)}

val test : {'n, 'n in {8,16}. atom('n)} -> int

function test(v) = f(v)
