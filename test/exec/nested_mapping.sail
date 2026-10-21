default Order dec

$include <prelude.sail>

enum E1 = {A1, B1}

enum E2 = {A2, B2}

val m1 : bits(1) <-> E1

mapping m1 = {
    0b0 <-> A1,
    0b1 <-> B1,
}

val m2 : E1 <-> E2

mapping m2 = {
    A1 <-> A2,
    B1 <-> B2,
}

val main : unit -> unit

function main() = {
    let x: int = match 0b10 {
        0b00 => 1,
        m1(m2(A2)) @ 0b0 => 2,
        _ => 3,
    };
    print_int("x = ", x);
    let y: int = match 0b10 {
        0b00 => 1,
        m1(m2(B2)) @ 0b0 => 2,
        _ => 3,
    };
    print_int("y = ", 2)
}
