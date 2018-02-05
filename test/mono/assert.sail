val f : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function f(n,m) = {
    assert(constraint('n in {8,16} & 'm < 'n));
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}

val g : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function g(n,m) = {
    assert(constraint('n in {8,16}) & 'm < 'n);
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}
val h : forall 'n 'm. (atom('n), atom('m)) -> unit effect {escape}

function h(n,m) = {
    assert(('n == 8 | 'n == 16) & 'm < 'n);
    let 'p = 2 * n in
    let x : bits('p) = replicate_bits(0b0,'p) in
    ()
}
