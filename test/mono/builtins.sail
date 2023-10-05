default Order dec

$include <smt.sail>
$include <arith.sail>
$include <flow.sail>
$include <vector_dec.sail>

val neq_vec = {lem: "neq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
function neq_vec (x, y) = not_bool(x == y)
overload operator != = {neq_vec}
val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

/* Test constant propagation's implementation of builtins
   TODO: need some way to check that everything has propagated. */

/* A function that constant propagation won't touch */
val launder : forall 'n. bits('n) -> bits('n)
function launder(x) = {
  assert(true);
  x
}

/* A function that constant propagation won't touch */
val launder_int : int -> int
function launder_int(x) = {
  assert(true);
  x
}

val test : bool -> unit

function test(b) = {
    let 'n : {'n, 'n in {8,16}. int('n)} = if b then 8 else 16;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    let x' : bits('n) = launder(x);
    let y : bits('n) = match 'n { 8 => 0x35, 16 => 0x5637 };
    let z : bits(8) = slice(x,5,3) @ slice(x,0,5);
    assert(slice(x,0,8) == z, "slice, concat, == by propagation");
    assert(x != y, "!= by propagation");
    assert(slice(x, 0, 4) == slice(x',0,4), "propagated slice == runtime slice");
    assert(0x3 == slice(y, 4, 4), "literal vs propagated middle slice");
    assert(UInt(x) == (match n { 8 => 18, 16 => 4660 }) : int, "UInt propagation vs literal");
    assert(shl_int(5,2) == shl_int(launder_int(5),2), "shl_int");
}

val run : unit -> unit

function run() = {
    test(true);
    test(false);
}
