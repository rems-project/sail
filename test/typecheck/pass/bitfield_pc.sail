$include <vector_dec.sail>

bitfield PC_t : vector(16, dec, bit) = {
  H : 15 .. 8,
  L :  7 .. 0
}
