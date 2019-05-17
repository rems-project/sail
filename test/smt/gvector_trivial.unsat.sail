default Order dec

$include <prelude.sail>

register R : vector(32, dec, bitvector(32, dec))

$property
function prop() -> bool = {
  R[0] = 0xDEAD_BEEF;
  R[0] == 0xDEAD_BEEF
}