default Order dec

$include <prelude.sail>

enum E = {A, B, C}

mapping foo : E <-> int = {
    A <-> 0,
    B <-> 1,
    C <-> 2
}

overload bar = {foo}

val main : unit -> unit

function main() = {
    print_int("foo(A) = ", foo(A));
    print_int("bar(A) = ", bar(A));
    match bar(0) {
        A => print_endline("got A"),
        _ => (),
    }
}
