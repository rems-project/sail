default Order dec

$include <prelude.sail>
$include <option.sail>

enum E = {A, B}

struct Foo = { bar : E }

val main : unit -> unit

function main() = {
    let x : Foo = struct { bar = B };
    match Some(x) {
      Some(struct { bar = A }) => (),
      None()  => (),
    }
}
