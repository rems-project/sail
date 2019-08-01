default Order dec

$include <prelude.sail>

register R : vector(32, dec, bitvector(32, dec))

type is_reg('n: Int) -> Bool = 0 <= 'n <= 31

$property
function prop forall 'n, is_reg('n). (n: int('n)) -> bool = {
  foreach (i from 0 to 31) {
    R[i] = 0xDEAD_BEEF;
  };
  R[n] == 0xDEAD_BEEF
}
