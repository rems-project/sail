register reg : bool

let A : {'n, 0 <= 'n & 'n <= 4. atom('n)} = 4

let B : range(0, 4) = A

val test : unit -> {|0, 1|} effect {rreg}

function test () = if reg then 0 else 1
