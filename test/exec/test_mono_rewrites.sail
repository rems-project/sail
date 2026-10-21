default Order dec
$include <prelude.sail>
$include <mono_rewrites.sail>

// Test the fused bitvector operations used by mono-rewrites.

val test_place_subrange : forall 'n 'm 'o 'z, 0 <= 'o <= 'm < 'n & 0 <= 'z.
  (bits('n), int('m), int('o), int('z)) -> bool
function test_place_subrange(xs,i,j,shift) = place_subrange(xs,i,j,shift) == vector_subrange(xs, i, j) @ sail_zeros(shift)

val test_place_slice : forall 'n 'o 'z, 0 <= 'o < 'n & 0 <= 'z.
  (bits('n), int, int('o), int('z)) -> bool
function test_place_slice(xs,i,j,shift) = place_slice(xs,i,j,shift) == slice(xs, i, j) @ sail_zeros(shift)

val test_subrange_subrange_concat : forall 'n 'o 'p 'm 'q 'r, 'n >= 0 & 'm >= 0 & 0 <= 'p & 'p <= 'o & 'o < 'n & 0 <= 'r & 'r <= 'q & 'q < 'm. (bits('n), atom('o), atom('p), bits('m), atom('q), atom('r)) -> bool
function test_subrange_subrange_concat(xs, i, j, ys, i', j') = subrange_subrange_concat(xs, i, j, ys, i', j') == vector_subrange(xs, i, j) @ vector_subrange(ys, i', j')

val test_slice_slice_concat : forall 'n 'm 'l 'p, 'n >= 0 & 'm >= 0 & 'l >= 0 & 'p >= 0.
  (bits('n), int, int('l), bits('m), int, int('p)) -> bool
function test_slice_slice_concat (xs, i, l, ys, i', l') = slice_slice_concat (xs, i, l, ys, i', l') == slice(xs, i, l) @ slice(ys, i', l')

val test_unsigned_subrange : forall 'n 'm 'o, 0 <= 'o <= 'm < 'n.  (bits('n), int('m), int('o)) -> bool
function test_unsigned_subrange(v, s, e) = unsigned(vector_subrange(v, s, e)) == unsigned_subrange(v, s, e)

val test_vector_update_subrange_from_subrange : forall 'n1 's1 'e1 'n2 's2 'e2, 0 <= 'e1 <= 's1 < 'n1 & 0 <= 'e2 <= 's2 < 'n2 & 's1 - 'e1 == 's2 - 'e2. (bits('n1), int('s1), int('e1), bits('n2), int('s2), int('e2)) -> bool
function test_vector_update_subrange_from_subrange(v1,s1,e1,v2,s2,e2) =
  vector_update_subrange_from_subrange(v1, s1, e1, v2, s2, e2) == update_subrange_bits(v1, s1, e1, vector_subrange(v2, s2, e2))

val test_vector_update_subrange_from_integer_subrange : forall 'n1 's1 'e1 's2 'e2, 0 <= 'e1 <= 's1 < 'n1 & 0 <= 'e2 <= 's2 & 's1 - 'e1 == 's2 - 'e2. (bits('n1), int('s1), int('e1), int, int('s2), int('e2)) -> bool
function test_vector_update_subrange_from_integer_subrange(v1,s1,e1,v2,s2,e2) =
  vector_update_subrange_from_integer_subrange(v1, s1, e1, v2, s2, e2) == update_subrange_bits(v1, s1, e1, get_slice_int(s2 - e2 + 1, v2, e2))

val test_set_subrange_zeros : forall 'n 's 'e, 0 <= 'e <= 's < 'n. (bits('n), int('s), int('e)) -> bool
function test_set_subrange_zeros(v, s, e) = set_subrange_zeros(v, s, e) == update_subrange_bits(v, s, e, sail_zeros(s - e + 1))

val test_subrange_subrange_eq : forall 'n 's1 'e1 's2 'e2, 0 <= 'e1 <= 's1 < 'n & 0 <= 'e2 <= 's2 < 'n & 's1 - 'e1 == 's2 - 'e2. (bits('n), int('s1), int('e1), bits('n), int('s2), int('e2)) -> bool
function test_subrange_subrange_eq(v1, s1, e1, v2, s2, e2) = subrange_subrange_eq(v1, s1, e1, v2, s2, e2) == (vector_subrange(v1, s1, e1) == vector_subrange(v2, s2, e2))

val test_is_zero_subrange : forall 'n 's 'e, 0 <= 'e <= 's < 'n. (bits('n), int('s), int('e)) -> bool
function test_is_zero_subrange(v, s, e) = is_zero_subrange(v, s, e) == (vector_subrange(v, s, e) == sail_zeros(s - e + 1))

val test_is_zero_slice : forall 'n 'l, 0 <= 'l & 0 <= 'n. (bits('n), int, int('l)) -> bool
function test_is_zero_slice(v, s, l) = is_zeros_slice(v, s, l) == (slice(v, s, l) == sail_zeros(l))

val test_is_ones_subrange : forall 'n 's 'e, 0 <= 'e <= 's < 'n. (bits('n), int('s), int('e)) -> bool
function test_is_ones_subrange(v, s, e) = is_ones_subrange(v, s, e) == (vector_subrange(v, s, e) == sail_ones(s - e + 1))

val test_is_ones_slice : forall 'n 'l, 0 <= 'l & 0 <= 'n. (bits('n), int, int('l)) -> bool
function test_is_ones_slice(v, s, l) = is_ones_slice(v, s, l) == (slice(v, s, l) == sail_ones(l))

val test_zext_subrange : forall 'm 'n 's 'e, 0 <= 'e <= 's < 'n & 's - 'e + 1 <= 'm. (int('m), bits('n), int('s), int('e)) -> bool
function test_zext_subrange(m, v, s, e) = zext_subrange(m, v, s, e) == sail_zero_extend(vector_subrange(v, s, e), m)

val test_zext_slice : forall 'm 'n 'l, 0 <= 'l <= 'm & 'l <= 'n. (int('m), bits('n), int, int('l)) -> bool
function test_zext_slice(m, v, s, l) = zext_slice(m, v, s, l) == sail_zero_extend(slice(v, s, l), m)

val test_sext_subrange : forall 'm 'n 's 'e, 0 <= 'e <= 's < 'n & 's - 'e + 1 <= 'm. (int('m), bits('n), int('s), int('e)) -> bool
function test_sext_subrange(m, v, s, e) = sext_subrange(m, v, s, e) == sail_sign_extend(vector_subrange(v, s, e), m)

val test_sext_slice : forall 'm 'n 'l, 0 <= 'l <= 'm & 'l <= 'n. (int('m), bits('n), int, int('l)) -> bool
function test_sext_slice(m, v, s, l) = sext_slice(m, v, s, l) == sail_sign_extend(slice(v, s, l), m)

val test_zext_ones : forall 'm 'n, 0 <= 'm <= 'n. (int('n), int('m)) -> bool
function test_zext_ones(m, n) = zext_ones(m, n) == sail_zero_extend(sail_ones(n), m)

val test_place_subrange_signed : forall 'n 'm 'o 'z 'l, 0 <= 'o <= 'm < 'n & 'm - 'o + 1 + 'z <= 'l & 0 <= 'z.
  (bits('n), int('m), int('o), int('z), int('l)) -> bool
function test_place_subrange_signed(xs,i,j,shift,l) = place_subrange_signed(xs,i,j,shift) == sail_sign_extend(vector_subrange(xs, i, j) @ sail_zeros(shift), l)

val test_place_slice_signed : forall 'n 'o 'z 'l, 0 <= 'o < 'n & 0 <= 'z & 'o + 'z <= 'l.
  (bits('n), int, int('o), int('z), int('l)) -> bool
function test_place_slice_signed(xs,i,j,shift,l) = place_slice_signed(xs,i,j,shift) == sail_sign_extend(slice(xs, i, j) @ sail_zeros(shift), l)

function main() -> unit = {
  assert(test_place_subrange(0x12, 2, 1, 5));
  assert(test_place_slice(0x12, 1, 2, 5));
  assert(test_subrange_subrange_concat(0x12, 2, 1, 0b11011011, 5, 3));
  assert(test_slice_slice_concat(0x12, 1, 2, 0b11011011, 3, 2));
  assert(test_unsigned_subrange(0x12, 2, 1));
  assert(test_unsigned_subrange(0x1c2, 7, 3));
  assert(test_vector_update_subrange_from_subrange(0x123, 8, 4, 0xabcd, 12, 8));
  assert(test_vector_update_subrange_from_integer_subrange(0x123, 8, 4, unsigned(0xabcd), 12, 8));
  assert(test_set_subrange_zeros(0x123, 6, 4));
  assert(test_subrange_subrange_eq(0x123, 7, 4, 0b010111001001, 5, 2));
  assert(test_subrange_subrange_eq(0x123, 7, 4, 0b010111001001, 7, 4));
  assert(test_is_zero_subrange(0x123, 5, 2));
  assert(test_is_zero_subrange(0x123, 4, 2));
  assert(test_is_zero_slice(0x123, 2, 3));
  assert(test_is_zero_slice(0x123, 2, 4));
  assert(test_is_ones_subrange(0x531, 5, 4));
  assert(test_is_ones_subrange(0x531, 7, 4));
  assert(test_is_ones_slice(0x531, 4, 2));
  assert(test_is_ones_slice(0x531, 4, 3));
  assert(test_zext_subrange(8, 0x030, 5, 4));
  assert(test_zext_subrange(8, 0x030, 7, 4));
  assert(test_zext_slice(8, 0x030, 4, 2));
  assert(test_zext_slice(8, 0x030, 4, 3));
  assert(test_sext_subrange(8, 0x030, 5, 4));
  assert(test_sext_subrange(8, 0x030, 7, 4));
  assert(test_sext_slice(8, 0x030, 4, 2));
  assert(test_sext_slice(8, 0x030, 4, 3));
  assert(test_zext_ones(6, 4));
  assert(test_place_subrange_signed(0x30, 5, 4, 3, 16));
  assert(test_place_subrange_signed(0x18, 5, 4, 3, 16));
  assert(test_place_slice_signed(0x30, 4, 2, 3, 16));
  assert(test_place_slice_signed(0x18, 4, 2, 3, 16));
}
