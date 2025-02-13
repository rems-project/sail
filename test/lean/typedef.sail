default Order dec
$include <prelude.sail>

type xlen       : Int = 64
type xlen_bytes : Int = 8
type xlenbits         = bits(xlen)

type my_bits('n) = bitvector('n)

val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTZ(m, v) = sail_zero_extend(v, m)

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTS(m, v) = sail_sign_extend(v, m)

