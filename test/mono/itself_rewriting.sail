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
val UInt = {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)
val bitvector_cast = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)
val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
overload operator > = {gt_int}

/* This was written to manually inspect that "let n = size_itself_int n in" gets
   added in the right places, but it's also worth running in case that gets
   broken. */

val needs_size_in_guard : forall 'n. atom('n) -> unit

function needs_size_in_guard(n if n > 8) = {
  let x : bits('n) = replicate_bits(0b0,n);
  ()
}
and needs_size_in_guard(n) = {
  let x : bits('n) = replicate_bits(0b1,n);
  ()
}

val no_size_in_guard : forall 'n. (atom('n), int) -> unit

function no_size_in_guard((n,m) if m > 8) = {
  let x : bits('n) = replicate_bits(0b0,n);
  ()
}
and no_size_in_guard(n,m) = {
  let x : bits('n) = replicate_bits(0b1,n);
  ()
}

val shadowed : forall 'n. atom('n) -> unit

function shadowed(n) = {
  let n = 8;
  let x : bits(8) = replicate_bits(0b0,n);
  ()
}

val willsplit : bool -> unit

function willsplit(x) = {
  let 'n : int = if x then 8 else 16;
  needs_size_in_guard(n);
  no_size_in_guard(n,n);
  shadowed(n);
}

val run : unit -> unit effect {escape}

function run () = {
  assert(true); /* To force us into the monad */
  willsplit(true);
  willsplit(false);
}