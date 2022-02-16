default Order dec

$sail_internal

$include <prelude.sail>

outcome test_outcome1 : forall 'n, 'n > 0. ('a, bits('n)) -> unit
with
  'a: Type
= {
    val to_bits : 'a -> bits(64)
}

outcome test_outcome2 : ('a, int) -> unit
with
  'a: Type

val instance_to_bits1 : bits(32) -> bits(64)

function instance_to_bits1(x) = {
    sail_zero_extend(x, 64)
}

val instance_to_bits2 : string -> bits(64)

function instance_to_bits2(_) = 0xFFFF_FFFF_FFFF_FFFF

instantiation test_outcome1 with
  to_bits = instance_to_bits1

instantiation test_outcome2
