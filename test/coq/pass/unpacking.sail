default Order dec

$include <prelude.sail>

val f : int -> {'n, 'n >= 0. int('n)} effect {rreg}
val g : int -> {'n, 'n >= 0. int('n)}

val test : unit -> int effect {rreg}

function test() = {
  let x1 : {'n, 'n >= 0. int('n)} = f(5);
  let x2 : int = f(6);
  let y1 : {'n, 'n >= 0. int('n)} = g(7);
  let y2 : int = g(8);
  x1 + x2 + y1 + y2
}
