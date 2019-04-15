$ifndef _MONO_REWRITES
$define _MONO_REWRITES

/* Definitions for use with the -mono_rewrites option */

$include <arith.sail>
$include <vector_dec.sail>

/* External definitions not in the usual asl prelude */

val extzv = "extz_vec" : forall 'n 'm. (implicit('m), vector('n, dec, bit)) -> vector('m, dec, bit) effect pure

val extsv = "exts_vec" : forall 'n 'm. (implicit('m), vector('n, dec, bit)) -> vector('m, dec, bit) effect pure

/* This is generated internally to deal with case splits which reveal the size
   of a bitvector */
val bitvector_cast_in = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_cast_out = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure

/* Definitions for the rewrites */

val is_zero_subrange : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect pure

function is_zero_subrange (xs, i, j) = {
  (xs & slice_mask(j, i-j+1)) == extzv([bitzero] : bits(1))
}

val is_zeros_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect pure

function is_zeros_slice (xs, i, l) = {
  (xs & slice_mask(i, l)) == extzv([bitzero] : bits(1))
}

val is_ones_subrange : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect pure

function is_ones_subrange (xs, i, j) = {
  let m : bits('n) = slice_mask(j,j-i+1) in
  (xs & m) == m
}

val is_ones_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect pure

function is_ones_slice (xs, i, j) = {
  let m : bits('n) = slice_mask(i,j) in
  (xs & m) == m
}

val slice_slice_concat : forall 'n 'm 'r, 'n >= 0 & 'm >= 0 & 'r >= 0.
  (implicit('r), bits('n), int, int, bits('m), int, int) -> bits('r) effect pure

function slice_slice_concat (r, xs, i, l, ys, i', l') = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  let ys = sail_shiftright(ys & slice_mask(i',l'), i') in
  sail_shiftleft(extzv(r, xs), l') | extzv(r, ys)
}

val slice_zeros_concat : forall 'n 'p 'q, 'n >= 0 & 'p + 'q >= 0.
  (bits('n), int, atom('p), atom('q)) -> bits('p + 'q) effect pure

function slice_zeros_concat (xs, i, l, l') = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  sail_shiftleft(extzv(l + l', xs), l')
}

/* Assumes initial vectors are of equal size */

val subrange_subrange_eq : forall 'n, 'n >= 0.
  (bits('n), int, int, bits('n), int, int) -> bool effect pure

function subrange_subrange_eq (xs, i, j, ys, i', j') = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  let ys = sail_shiftright(ys & slice_mask(j',i'-j'+1), j') in
  xs == ys
}

val subrange_subrange_concat : forall 'n 'o 'p 'm 'q 'r 's, 's >= 0 & 'n >= 0 & 'm >= 0.
  (implicit('s), bits('n), atom('o), atom('p), bits('m), atom('q), atom('r)) -> bits('s) effect pure

function subrange_subrange_concat (s, xs, i, j, ys, i', j') = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  let ys = sail_shiftright(ys & slice_mask(j',i'-j'+1), j) in
  sail_shiftleft(extzv(s, xs), i' - j' + 1) | extzv(s, ys)
}

val place_subrange : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m) effect pure

function place_subrange(m,xs,i,j,shift) = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  sail_shiftleft(extzv(m, xs), shift)
}

val place_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m) effect pure

function place_slice(m,xs,i,l,shift) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  sail_shiftleft(extzv(m, xs), shift)
}

val set_slice_zeros : forall 'n, 'n >= 0.
  (atom('n), bits('n), int, int) -> bits('n) effect pure

function set_slice_zeros(n, xs, i, l) = {
  let ys : bits('n) = slice_mask(n, i, l) in
  xs & not_vec(ys)
}

val zext_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m) effect pure

function zext_slice(m,xs,i,l) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  extzv(m, xs)
}

val sext_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m) effect pure

function sext_slice(m,xs,i,l) = {
  let xs = sail_arith_shiftright(sail_shiftleft((xs & slice_mask(i,l)), ('n - i - l)), 'n - l) in
  extsv(m, xs)
}

val place_slice_signed : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m) effect pure

function place_slice_signed(m,xs,i,l,shift) = {
  sail_shiftleft(sext_slice(m, xs, i, l), shift)
}

/* This has different names in the aarch64 prelude (UInt) and the other
   preludes (unsigned).  To avoid variable name clashes, we redeclare it
   here with a suitably awkward name. */
val _builtin_unsigned = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> {'m, 0 <= 'm < 2 ^ 'n. int('m)}

/* There are different implementation choices for division and remainder, but
   they agree on positive values.  We use this here to give more precise return
   types for unsigned_slice and unsigned_subrange. */

val _builtin_mod_nat = {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod",
  c: "tmod_int",
  coq: "Z.rem"
} : forall 'n 'm, 'n >= 0 & 'm >= 0. (int('n), int('m)) -> {'r, 0 <= 'r < 'm. int('r)}

/* Below we need the fact that 2 ^ 'n >= 0, so we axiomatise it in the return
   type of pow2, as SMT solvers tend to have problems with exponentiation. */
val _builtin_pow2 = "pow2" : forall 'n, 'n >= 0. int('n) -> {'m, 'm == 2 ^ 'n & 'm >= 0. int('m)}

val unsigned_slice : forall 'n 'l, 'n >= 0 & 'l >= 0.
  (bits('n), int, int('l)) -> {'m, 0 <= 'm < 2 ^ 'l. int('m)} effect pure

function unsigned_slice(xs,i,l) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  _builtin_mod_nat(_builtin_unsigned(xs), _builtin_pow2(l))
}

val unsigned_subrange : forall 'n 'i 'j, 'n >= 0 & ('i - 'j) >= 0.
  (bits('n), int('i), int('j)) -> {'m, 0 <= 'm < 2 ^ ('i - 'j + 1). int('m)} effect pure

function unsigned_subrange(xs,i,j) = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), i) in
  _builtin_mod_nat(_builtin_unsigned(xs), _builtin_pow2(i - j + 1))
}


val zext_ones : forall 'n, 'n >= 0. (implicit('n), int) -> bits('n) effect pure

function zext_ones(n, m) = {
  let v : bits('n) = extsv([bitone] : bits(1)) in
  sail_shiftright(v, n - m)
}

$endif
