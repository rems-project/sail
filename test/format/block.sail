default Order dec

$include <prelude.sail>

val foo : unit -> unit

function foo() = {
    print_endline("string1"); // comment
    print_endline("string2");

    ();
    ();

    let x = call_function_with_a_long_name(and_long_arguments, 1, 2, 3, 4, // foo
    5, 6, 7, /* comment */ 8);

    print_endline("string3")
}
