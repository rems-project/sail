default Order dec

$include <prelude.sail>

enum E = {A, B}

mapping foo : bits(1) <-> E = {
  0b0 <-> A,
  0b1 <-> B,
}

val bar : unit -> unit

// Currently we only check mapping-free patterns, so this should warn for A
function bar() = {
    match A {
        foo(0b0) => print_endline("1"),
        B => print_endline("2"),
    }
}
