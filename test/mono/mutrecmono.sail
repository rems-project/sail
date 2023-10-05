default Order dec
$include <prelude.sail>

val extz : forall 'n 'm, 'n >= 0 & 'm >= 0. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extz(m,v) = sail_mask(m,v)
val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)


val a : {8,16,32} -> int
val b : {8,16,32} -> int

function a 'n = if n == 8 then b(n) else let x : bits('n) = extz(0x12) in UInt(x)
function b 'n = if n == 32 then a(n) else let x : bits('n) = extz(0x34) in UInt(x)

val run : unit -> unit

function run () = {
  assert(a(8) == 52);
  assert(a(16) == 18);
  assert(a(32) == 18);
  assert(b(8) == 52);
  assert(b(16) == 52);
  assert(a(32) == 18);
}
