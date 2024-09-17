default Order dec

$include <smt.sail>
$include <prelude.sail>

type xlen : Int = abs(-2)

bitfield foo : bits(xlen) = {
  A : 0,
}
