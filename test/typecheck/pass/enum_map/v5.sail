default Order dec

$include <prelude.sail>

enum E with as_bits -> bits(16) = {
  A => (0xFFFF, "A"),
  B => (0x0001, "B"),
  C => (sail_zeros(16), "C")
}

enum F with as_bits -> bits(16) = {
  A2 => 0xFFFF,
  B2 => 0x0001,
  C2 => sail_zeros(16)
}

function main() -> unit = {
  print_bits("A = ", E_as_bits(A));
  print_bits("A2 = ", F_as_bits(A2))
}
