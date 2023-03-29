default Order dec

val foo : forall 'n, 'n in {16, 32, 64}. int('n) -> unit

function foo(n) = match n {
    16 => (),
    32 => (),
}
