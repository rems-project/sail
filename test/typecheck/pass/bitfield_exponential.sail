default Order dec

$include <prelude.sail>

type xlen : Int = 2 ^ 2

bitfield foo : bits(xlen) = {
  A : 0,
}
