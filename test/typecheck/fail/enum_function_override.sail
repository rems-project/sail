default Order dec
$include <prelude.sail>

val bar : unit -> unit

function bar() = ()

$[enum_number_conversions { to_enum = bar, from_enum = baz }]
enum Foo = A | B | C

// Force a type error to check we get a warning...
let x : int(0) = "string"
