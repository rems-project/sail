default Order dec
$include <prelude.sail>

$option --abstract-types

$span start XLEN
type xlen : Int

constraint xlen in {32, 64}
$span end

register X1 : bits(xlen)

val rv32_only : unit -> unit
