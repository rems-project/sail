default Order dec

$include <vector_dec.sail>

bitfield PC_t : bitvector(16, dec) = {
  H : 15 .. 8,
  L :  7 .. 0
}
