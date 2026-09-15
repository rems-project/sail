default Order dec
$include <prelude.sail>

// Dependently typed targets often merge type and definition namespaces, so test shadowing types.

type my_bits = bits(32)

function my_bits(x : int) -> my_bits = add_bits_int(sail_zeros(32) : my_bits, x)

type my_other_bits = bits(16)

function main() -> unit = {
  assert(my_bits(64) == (0x00000040 : my_bits));
  let my_other_bits : bits(16) = 0x1234;
  assert(my_other_bits == (0x1234 : my_other_bits));
}
