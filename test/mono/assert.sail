default Order dec
$include <prelude.sail>
$include <smt.sail>

/* Tests set constraints in different constraints */

val f : forall 'n 'm. (int('n), int('m)) -> unit

function f(n,m) = {
    assert(constraint('n in {8,16} & 'm < 'n), "nconstraint");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val f' : forall 'n 'm. (int('n), int('m)) -> unit

function f'(n,m) = {
    assert(constraint(('n == 8 | 'n == 16) & 'm < 'n), "nconstraint");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val g : forall 'n 'm. (int('n), int('m)) -> unit

function g(n,m) = {
    assert(constraint('n in {8,16}) & 'm < 'n, "set and exp");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}
val h : forall 'n 'm. (int('n), int('m)) -> unit

function h(n,m) = {
    assert(('n == 8 | 'n == 16) & 'm < 'n, "all exp");
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val run : unit -> unit

function run () = {
    f(8,3);
    f'(8,3);
    g(16,3);
    h(8,3);
}
