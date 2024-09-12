default Order dec

$include <prelude.sail>

union Foo = {
  A : int,
  B : string
}

val main : unit -> unit

function main() = {
    var x = A(3);
    x.B = "Hello, World!"
}
