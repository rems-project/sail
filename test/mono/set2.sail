default Order dec

(* A function which is merely parametrised by a size does not need to be
   monomorphised *)

val forall 'n, 'n in {32,64}. ([:'n:], bit[32]) -> bit[64] parametric

function parametric(n,v) = {
  let (bit['n]) x = exts(v) in
  extz(x)
}

(* But if we do a calculation on the size then we'll need to case split *)

val forall 'n, 'n in {16,32}. ([:'n:], bit[32]) -> bit[64] depends

function depends(n,v) = {
  let 'm = 2 * n in
  let (bit['m]) x = exts(v) in
  extz(x)
}

val unit -> bool effect pure run

function run () =
  parametric(32,0x80000000) == 0x0000000080000000 &
  parametric(64,0x80000000) == 0xffffffff80000000 &
  depends(16,0x80000000) == 0x0000000080000000 &
  depends(32,0x80000000) == 0xffffffff80000000
