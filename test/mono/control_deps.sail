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
val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extz : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extz(v) = extz_vec(sizeof('m),v)
val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)
overload append = {bitvector_concat}
val bitvector_cast = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)
overload length = {bitvector_length}

/* Test monomorphisation control dependencies */

val f : (bool,bool) -> unit

function f(nosplit,split) = {
  if nosplit then {
    let 'x : {'x, true. atom('x)} = if split then 16 else 32 in
    let v : bits('x) = extz(0b0) in
    ()
  } else ()
}

val g : (bool,bool) -> unit

function g(split,nosplit) = {
  x : {'x, true. atom('x)} = 16;
  y : {'y, true. atom('y)} = 16;
  if split then
    x = 32
  else
    ();
  if nosplit then
    y = 32
  else
    ();
  let 'z : {'z, true. atom('z)} = x in
  let v : bits('z)= extz(0b0) in
  ()
}

type exception = unit

val h : bool -> unit effect {escape}

/* Note: we don't really need to split on b, but it's awkward to avoid.
   The important bit is not to overreact to the exception. */
/* While the case splitting currently works, it doesn't yet generate a fake size
   for 'x or remove the dead code that needs one
function h(b) = {
  let 'x : {'x, true. atom('x)} =
    if b then 16 else throw () in
  let v : bits('x) = extz(0b0) in
  ()
}
*/

val run : unit -> unit effect {escape}

function run () = {
  assert(true);
  f(false,false);
  f(false,true);
  g(false,false);
  g(false,true);
/*  h(true);*/
}