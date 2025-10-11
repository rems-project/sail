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

val bitvector_len : bits(16) -> nat
function bitvector_len(x) = {
  length (x)
}

val bitvector_sign_extend : bits(16) -> bits(32)
function bitvector_sign_extend(x) = {
  sail_sign_extend (x, 32)
}

val bitvector_zero_extend : bits(16) -> bits(32)
function bitvector_zero_extend(x) = {
  sail_zero_extend (x, 32)
}

val bitvector_truncate : bits(32) -> bits(16)
function bitvector_truncate(x) = {
  truncate (x, 16)
}

val bitvector_truncateLSB : bits(32) -> bits(16)
function bitvector_truncateLSB(x) = {
  truncateLSB (x, 16)
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

val bitvector_unsigned : bits(16) -> nat
function bitvector_unsigned(x) = {
  unsigned (x)
}

val bitvector_signed : bits(16) -> int
function bitvector_signed(x) = {
  signed (x)
}

val bitvector_access' : (bits(16), range(0,15)) -> bit
function bitvector_access'(x, i) = {
  x[i]
}

val bitvector_plus_int : (bits(16), int) -> bits(16)
function bitvector_plus_int(x, i) = {
  x + i
}

function bitvector_literal(x: bit, y: bit) -> bits(2) = {
  [x, y]
}

function vector_literal(x: int, y: int) -> vector(2, int) = {
  [x, y]
}

