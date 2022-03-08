/* from prelude */
default Order dec

$include <flow.sail>

type bits ('n : Int) = bitvector('n, dec)

type xlen : Int       = 64
type xlen_bytes : Int = 8
type xlenbits = bits(xlen)

val sign_extend = pure "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)
val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTS(m, v) = sign_extend(v, m)

val extend : forall 'n, 'n <= xlen_bytes. (bool, bits(8 * 'n)) -> xlenbits

function extend(flag, value) = EXTS(value)
