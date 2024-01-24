default Order dec

$include <prelude.sail>
$include <smt.sail>

type xlen : Int = mod(5, 3)

bitfield foo : bits(xlen) = {
  A : 0,
}
