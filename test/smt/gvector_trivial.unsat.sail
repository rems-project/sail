default Order dec

$include <prelude.sail>

register R : vector(32, dec, vector(32, dec, bit))

$property
function prop() -> bool = {
  R[0] = 0xDEAD_BEEF;
  R[0] == 0xDEAD_BEEF
}