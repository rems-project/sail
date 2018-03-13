$include <smt.sail>
$include <flow.sail>
default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extz : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extz(v) = extz_vec(sizeof('m),v)
val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)


val a : {|8,16,32|} -> int
val b : {|8,16,32|} -> int

function a 'n = if n == 8 then b(n) else let x : bits('n) = extz(0x12) in UInt(x)
function b 'n = if n == 32 then a(n) else let x : bits('n) = extz(0x34) in UInt(x)

val run : unit -> unit effect {escape}

function run () = {
  assert(a(8) == 52);
  assert(a(16) == 18);
  assert(a(32) == 18);
  assert(b(8) == 52);
  assert(b(16) == 52);
  assert(a(32) == 18);
}