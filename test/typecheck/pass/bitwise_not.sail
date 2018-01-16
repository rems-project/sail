val bitwise_not : forall ('m : Int) ('o : Order).
  vector('m, 'o, bit) -> vector('m, 'o, bit)

default Order dec

val test : vector(5, dec, bit) -> vector(5, dec, bit)

function test x : vector(5, dec, bit) = bitwise_not(x)
