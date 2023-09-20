$option -dmagic_hash

default Order dec

$include <prelude.sail>

val foo : unit -> unit

function foo() = {
    ();
    let x = { s with foo = 0xFFFF, bar = 0b1 }
}

val bar : unit -> int

function baz() = {
    ();
    let some_long_named_variable_to_break_the_line = { function_modify_the_struct(struct_with_a_long_name, x) with foo = 0xFFFF, bar = 0b1 };
    *R = baz; // trailing comment


    return 3 + (return 4)
}

scattered function /* comment */quux

function clause quux 0b0000_0000 = ()

end /* comment */ quux

end quux

enum E = A | B | C
enum E with f -> unit, g -> unit = {
  A => (),
  B
}

enum E with f -> very_long_type_that_will_trigger_a_linebreak, g -> another_very_long_type_name, h -> a_third_very_long_type_name, = {
  A => (),
  B
}

function has_loops() = {
    foreach (n from 1 to 3) {
        ()
    };
    foreach (n from 3 downto 1) {
        ()
    };
    foreach (n from 0 to 4 by 2) {
        ()
    };
    foreach (n from 10000000000000000000000000000000 to 444444444444444444444444444444444444444444444444444444444444) {
        ()
    };
    while true do ();
    while true do {
        ()
    };
    repeat termination_measure { foo } () until true
}

type foo = bar
