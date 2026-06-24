default Order dec

val foo : forall 'n, 'n >= 16. bitvector('n) -> unit

let _ = foo(0x0)
