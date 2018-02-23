$include <smt.sail>
$include <flow.sail>
default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
overload operator < = {lt_atom, lt_int}

/* Test splitting required because there's a size calculation in the function */

val foo : forall 'n. atom('n) -> unit effect {escape}

function foo(n) = {
  assert(constraint('n in {2,4}));
  let 'm = 8 * n in
  let x : bits('m) = replicate_bits(0b0,m) in
  let y : bits('n) = replicate_bits(0b0,n) in
  ()
}

val run : unit -> unit effect {escape}

function run () = {
    foo(2);
    foo(4);
}