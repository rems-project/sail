default Order dec

$include <prelude.sail>

function extern_const() -> bitvector(64) = {
  return 0xFFFF_0000_1234_0000
}

function extern_add() -> bitvector(16) = {
  return 0xFFFF + 0x1234
}

function extern_replicate_bits() -> bitvector(64) = {
  return replicate_bits(0x1234, 4)
}

function extern_slice(x : bitvector(16)) -> bitvector(4) = {
  return slice(x, 2, 4)
}

function extern_vector_length(x : vector(3, int)) -> int = {
  return length(x)
}

function extern_count_leading_zeros() -> int = {
  return count_leading_zeros(0x00FF0FF0)
}

function extern_count_trailing_zeros() -> int = {
  return count_trailing_zeros(0x00FF0FF0)
}

function extern_arith_shiftright() -> bitvector(32) = {
  return sail_arith_shiftright(0xDEADBEEF, 4)
}

