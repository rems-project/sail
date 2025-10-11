default Order dec

$include <prelude.sail>

bitfield cr_type : bits(8) = {
  CR0 : 7 .. 4,
  LT  : 7,
  GT  : 6,
  CR1 : 3 .. 2,
  CR3 : 1 .. 0
}

register R : cr_type
