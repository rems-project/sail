default Order dec

$include <prelude.sail>

val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTZ(m, v) = sail_zero_extend(v, m)

val foo : bits(8) -> bits(16)
function foo x = {
  EXTZ(x)
}

val slice_mask2 : forall 'n, 'n >= 0. (implicit('n), bits('n), bits('n), bool) -> bits('n)
function slice_mask2(n,i,l,b) =
  if b then {
    i
  } else {
    let one : bits('n) = EXTZ(n, l) in
    one + one
  }
