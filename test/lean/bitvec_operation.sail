default Order dec

$include <prelude.sail>

val bitvector_eq : (bits(16), bits(16)) -> bool
function bitvector_eq(x, y) = {
  x == y
}

val bitvector_neq : (bits(16), bits(16)) -> bool
function bitvector_neq(x, y) = {
  x != y
}

val bitvector_append : (bits(16), bits(16)) -> bits(32)
function bitvector_append(x, y) = {
  append (x, y)
}

val bitvector_add : (bits(16), bits(16)) -> bits(16)
function bitvector_add(x, y) = {
  x + y
}

val bitvector_sub : (bits(16), bits(16)) -> bits(16)
function bitvector_sub(x, y) = {
  sub_bits (x, y)
}

val bitvector_not : bits(16) -> bits(16)
function bitvector_not(x) = {
  not_vec (x)
}

val bitvector_and : (bits(16), bits(16)) -> bits(16)
function bitvector_and(x, y) = {
  x & y
}

val bitvector_or : (bits(16), bits(16)) -> bits(16)
function bitvector_or(x, y) = {
  x | y
}

val bitvector_xor : (bits(16), bits(16)) -> bits(16)
function bitvector_xor(x, y) = {
  xor_vec (x, y)
}

