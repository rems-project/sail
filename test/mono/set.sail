default Order dec
$include <prelude.sail>
val "extz_vec" : forall 'n 'm. (atom('m),bitvector('n, dec)) -> bitvector('m, dec) effect pure
val extz : forall 'n 'm. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extz(m,v) = extz_vec(m,v)
val "exts_vec" : forall 'n 'm. (atom('m),bitvector('n, dec)) -> bitvector('m, dec) effect pure
val exts : forall 'n 'm. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function exts(m,v) = exts_vec(m,v)

/* A function which is merely parametrised by a size does not need to be
   monomorphised */

val parametric : forall 'n, 'n in {32,64}. atom('n) -> bits(64)

function parametric(n) = {
  let x : bits('n) = exts(0x80000000) in
  extz(x)
}

/* But if we do a calculation on the size then we'll need to case split */

val depends : forall 'n, 'n in {16,32}. atom('n) -> bits(64)

function depends(n) = {
  let 'm = 2 * n in
  let x : bits('m) = exts(0x80000000) in
  extz(x)
}

val run : unit -> unit effect {escape}

function run () = {
  assert(parametric(32) == 0x0000000080000000);
  assert(parametric(64) == 0xffffffff80000000);
  assert(depends(16) == 0x0000000080000000);
  assert(depends(32) == 0xffffffff80000000);
}
