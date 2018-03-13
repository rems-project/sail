$include <smt.sail>
$include <flow.sail>
default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val neq_vec = {lem: "neq"} : forall 'n. (bits('n), bits('n)) -> bool
function neq_vec (x, y) = not_bool(eq_vec(x, y))
overload operator != = {neq_atom, neq_vec}
val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
/*val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extz : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extz(v) = extz_vec(sizeof('m),v)
val "exts_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val exts : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function exts(v) = exts_vec(sizeof('m),v)*/
val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)
val bitvector_cast = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

/* Test constant propagation on some variable patterns in let expressions */

val test : bool -> unit effect {escape}

function test(b) = {
    let 'n : {|8,16|} = if b then 8 else 16;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(UInt(x) == (match n { 8 => 18, 16 => 4660 }), "UInt");
}

val test2 : bool -> unit effect {escape}

function test2(b) = {
    let 'n = (if b then 8 else 16) : {|8,16|};
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(UInt(x) == (match n { 8 => 18, 16 => 4660 }), "UInt");
}

val test_mult : {|4,8|} -> unit effect {escape}

function test_mult('m) = {
    let 'n = 2 * 'm;
    let x : bits('n) = match 'n { 8 => 0x12, 16 => 0x1234 };
    assert(UInt(x) == (match n { 8 => 18, 16 => 4660 }), "UInt");
}

val run : unit -> unit effect {escape}

function run() = {
    test(true);
    test(false);
    test2(true);
    test2(false);
    test_mult(4);
    test_mult(8);
}