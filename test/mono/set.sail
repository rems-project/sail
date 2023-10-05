default Order dec
$include <prelude.sail>

val extz : forall 'n 'm, 'n >= 0 & 'm >= 'n. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extz(m,v) = sail_zero_extend(v, m)

val exts : forall 'n 'm, 'n >= 0 & 'm >= 'n. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function exts(m,v) = sail_sign_extend(v, m)

/* A function which is merely parametrised by a size does not need to be
   monomorphised */

val parametric : forall 'n, 'n in {32,64}. int('n) -> bits(64)

function parametric(n) = {
  let x : bits('n) = exts(0x80000000) in
  extz(x)
}

/* But if we do a calculation on the size then we'll need to case split */

val depends : forall 'n, 'n in {16,32}. int('n) -> bits(64)

function depends(n) = {
  let 'm = 2 * n in
  let x : bits('m) = exts(0x80000000) in
  extz(x)
}

val run : unit -> unit

function run () = {
  assert(parametric(32) == 0x0000000080000000);
  assert(parametric(64) == 0xffffffff80000000);
  assert(depends(16) == 0x0000000080000000);
  assert(depends(32) == 0xffffffff80000000);
}
