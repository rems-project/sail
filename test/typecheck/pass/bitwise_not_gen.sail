val bitwise_not : forall ('m : Int) ('o : Order).
  vector('m, 'o, bit) -> vector('m, 'o, bit)

default Order dec

val test : forall 'n.
  vector('n, dec, bit) -> vector('n, dec, bit)

function test x : vector('n, dec, bit) = bitwise_not(bitwise_not(x))
