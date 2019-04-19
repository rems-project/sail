default Order dec

$include <prelude.sail>

register R0 : bits(32)
register R1 : bits(32)
register R2 : bits(32)
register R3 : bits(32)

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

let GPRs = [ref R3, ref R2, ref R1, ref R0]

function wGPR(n: range(0, 3), v: bits(32)) -> unit = {
  (*GPRs[n]) = v
}

function rGPR(n: range(0, 3)) -> bits(32) = {
  reg_deref(GPRs[n])
}

overload R = {wGPR, rGPR}

$property
function prop() -> bool = {
  R(0) = 0x1234_5678;
  R(0) == 0x1234_5678
}
