val bitwise_not : forall ('n : Int) ('o : Order).
  vector('n, 'o, bit) -> vector('n, 'o, bit)

default Order dec

val test : vector(5, dec, bit) -> vector(5, dec, bit)

function test x : vector(5, dec, bit) = bitwise_not(bitwise_not(bitwise_not(x)))
