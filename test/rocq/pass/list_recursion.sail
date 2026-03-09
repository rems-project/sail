/* Example from RISC-V of a structurally recursive function that
doesn't need a measure. */

default Order dec
$include <prelude.sail>

overload operator - = { sub_bits }

val sbox_lookup : (bits(8), list(bits(8))) -> bits(8)
function sbox_lookup(x, table) = {
  match (x, table) {
    (0x00, t0::tn) => t0,
    (   y, t0::tn) => sbox_lookup(x - 0x01, tn)
  }
}

