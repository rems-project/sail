default Order dec

$include <prelude.sail>

struct foo('m, 'n) = {
    f1 : option(bits('n)),
    f2 : int('m),
}

val bar : forall 'n, 'n in {0, 5}. int('n) -> unit

function bar(n) = {
    match (struct { f1 = Some(0b00), f2 = n } : foo('n, 2)) {
        struct { f1 = Some(_), f2 = 0 } => (),
        struct { f2 = 0, _ } => (),
        struct { f1 = None(), f2 = 0 } => (),
    }
}
