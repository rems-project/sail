bitfield cr : bitvector(8,dec) = {
  CR0 : 7 .. 4,
  LT  : 7,
  GT  : 6,
  CR1 : 3 .. 2,
  CR3 : 1 .. 0
}
register CR : cr
