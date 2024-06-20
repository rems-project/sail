default Order dec
$include <prelude.sail>

val bar : unit -> unit

function bar() = ()

$[enum_functions { to_enum = bar, from_enum = baz }]
enum Foo = A | B | C
