default Order dec

$include <prelude.sail>

val foo : bits(32) -> unit

function foo(xs) = {
  match xs {
    _ : bits(33) @ _ : bits(-1) => ()
  }
}
