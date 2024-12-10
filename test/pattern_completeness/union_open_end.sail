default Order dec

$include <prelude.sail>

scattered union U

union clause U = A : int

register R : U = A(0)

union clause U = B : string

end U

val foo : unit -> unit

function foo() = {
  match R {
    A(0) => (),
    A(_) => (),
    B(s) => print_endline(s),
  }
}
