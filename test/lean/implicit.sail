default Order dec

$include <prelude.sail>

val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTZ(m, v) = sail_zero_extend(v, m)

val foo : bits(8) -> bits(16)
function foo x = {
  EXTZ(x)
}
