default Order dec

$include <prelude.sail>

struct foo = {
    f1 : int,
    f2 : int,
    f3 : int,
}

function bar(x: foo) -> unit = {
    match x {
        struct { f1 = x, f1 = y, _ } => ()
    }
}
