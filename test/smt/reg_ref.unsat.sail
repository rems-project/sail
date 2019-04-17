default Order dec

$include <prelude.sail>

val "reg_deref" : forall ('a: Type). register('a) -> 'a effect {rreg}

register R0 : bits(32)
register R1 : bits(32)
register R2 : bits(32)
register R3 : bits(32)

let GPRs = [ref R3, ref R2, ref R1, ref R0]

$property
function prop() -> bool = {
  R0 = 0xDEAD_BEEF;
  reg_deref(GPRs[0]) == 0xDEAD_BEEF
}