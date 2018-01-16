default Order dec

val vector_subrange : forall ('n : Int) ('m : Int) ('o : Int).
  (vector('n, dec, bit), atom('m), atom('o)) -> vector('m - ('o - 1), dec, bit)

val test : vector(6, dec, bit) -> unit

function test xs = {
  len : int = 4;
  len : {'n, true. atom('n)} = 5;
  ys = xs[len .. 0];
  ()
}
