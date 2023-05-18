default Order dec

$include <prelude.sail>

struct foo = {
    f1 : int,
    f2 : int,
    f3 : int,
}

function bar(x: foo) -> unit = {
    match x {
        struct { _ } => ()
    };
    match x {
        struct { f1 = _, f2 = _, f3 = _ } => ()
    };
    match x {
        struct { f1 = 0, f2 = _, _ } => (),
        struct { f1 = _, f2 = 0, _ } => (),
        struct { f1 = x, f2 = y, _ } => (),
    }
}

struct baz('n), 'n in {32, 64} = {
     len : int('n),
     value : bits('n),
}

function quux forall 'n, 'n == 32. (x: baz('n)) -> unit = {
    match x {
        struct { len = 32, value = _ } => ()
    }
}

function quux2 forall 'n, 'n in {32, 64}. (x: baz('n)) -> unit = {
    match x {
        struct { len = 32, value = _ } => (),
        struct { len = 64, _ } => (),
    }
}
