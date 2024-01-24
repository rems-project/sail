default Order dec

$include <prelude.sail>

type xlen : Int = abs(-2)

bitfield foo : bits(xlen) = {
  A : 0,
}
