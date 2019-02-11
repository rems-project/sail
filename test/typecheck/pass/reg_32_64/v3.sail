default Order dec

$include <prelude.sail>

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

register R0 : bits(64)
register R1 : bits(64)
register R2 : bits(64)
register R3 : bits(64)

let GPRs : vector(4, dec, register(bits(64))) = [ref R3, ref R2, ref R1, ref R0]

type regno('r: Int) -> Bool = 0 <= 'r <= 3

val set_R : forall 'r 'd, regno('r) & 'd in {32, 64}.
  (int('r), bits('d)) -> unit effect {wreg}

function set_R(r, data) = {
  let R = GPRs[r];
  (*R)['d - 1 .. 0] = data
}

val get_R : forall 'r 'd, regno('r) & 'd in {32, 64}.
  (implicit('d), int('r)) -> bits('d) effect {rreg}

function get_R(_, r) = {
  let R = GPRs[r];
  reg_deref(R)['d - 1 .. 0]
}

overload R = {set_R, get_R}

function main() -> unit = {
  R(0) = 0xCAFE_CAFE_0000_0000;
  R(0) = 0xFFFF_FFFF;
  print_bits("R = ", R(0) : bits(64));
  print_bits("R = ", R(0) : bits(32))
}
