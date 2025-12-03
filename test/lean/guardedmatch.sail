/* A pattern matching with guards example derived from RISC-V.

   The guarded patterns rewrite was introducing a bogus fallthrough
   case which resulted in an empty pattern match.
*/

default Order dec
$include <prelude.sail>

$option --config guardedmatch.json

type xlen : Int = config base.xlen
constraint xlen in {32, 64}
let xlen = sizeof(xlen)

val f : (bits(12), int) -> int

function f(0x200, v) = 0
and f((0x300, v) if xlen == 32) = 1
and f((0x300, v) if xlen == 64) = 2
and f((0x308, v) if xlen == 32) = 3
and f((0x310, v) if xlen == 32) = 4
and f((0x310, v) if xlen == 64) = 5
and f(_, _) = 7
