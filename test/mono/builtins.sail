$include <smt.sail>
$include <flow.sail>
$include <vector_dec.sail>

default Order dec
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
val launder : forall 'n. bits('n) -> bits('n) effect {escape}
function launder(x) = {
  assert(true);
  x
}

val test : bool -> unit effect {escape}

function test(b) = {
    let 'n : {'n, 'n in {8,16}. atom('n)} = if b then 8 else 16;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    let x' : bits('n) = launder(x);
    let y : bits('n) = match 'n { 8 => 0x35, 16 => 0x5637 };
    assert(x != y, "!= by propagation");
    assert(slice(x, 0, 4) == slice(x',0,4), "propagated slice == runtime slice");
    assert(0x3 == slice(y, 4, 4), "literal vs propagated middle slice");
    assert(UInt(x) == (match n { 8 => 18, 16 => 4660 }), "UInt propagation vs literal");
}

val run : unit -> unit effect {escape}

function run() = {
    test(true);
    test(false);
}