default Order dec

$sail_internal

$include <prelude.sail>

$target_set emulator c ocaml interpreter

struct Foo = {
    bar : option(int)
}

val main : unit -> unit

outcome test: 'a -> unit with 'a: Type = {
    impl emulator(_) = ()
}

instantiation test with
    'a = option(Foo)

function main() = {
    test(Some(struct { bar = Some(0) }));
    print_endline("ok");
}
