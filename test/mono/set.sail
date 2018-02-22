default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
val eq_int = {ocaml: "eq_int", lem: "eq"} : (int, int) -> bool
overload operator == = {eq_int, eq_vec}
val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extz : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extz(v) = extz_vec(sizeof('m),v)
val "exts_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val exts : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function exts(v) = exts_vec(sizeof('m),v)

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
