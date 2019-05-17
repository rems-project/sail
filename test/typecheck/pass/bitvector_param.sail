default Order dec

$include <flow.sail>
$include <vector_dec.sail>

type xlen : Int = 64
type ylen : Int = 1

type xlenbits = bits(xlen)

bitfield Mstatus : xlenbits = {
  SD  : xlen - ylen,
  SXL : xlen - ylen - 1 .. xlen - ylen - 3
}
register mstatus : Mstatus
