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

/* Tests set constraints in different constraints */

val f : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function f(n,m) = {
    assert(constraint('n in {8,16} & 'm < 'n), "nconstraint");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val f' : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function f'(n,m) = {
    assert(constraint(('n == 8 | 'n == 16) & 'm < 'n), "nconstraint");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val g : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function g(n,m) = {
    assert(constraint('n in {8,16}) & 'm < 'n, "set and exp");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}
val h : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function h(n,m) = {
    assert(('n == 8 | 'n == 16) & 'm < 'n, "all exp");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val run : unit -> unit effect {escape}

function run () = {
    f(8,3);
    f'(8,3);
    g(16,3);
    h(8,3);
}
