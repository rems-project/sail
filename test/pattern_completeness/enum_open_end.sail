default Order dec

$include <prelude.sail>

scattered enum E

enum clause E = A

register R : E = A

enum clause E = B

end E

val foo : unit -> unit

function foo() = {
  match R {
    A => (),
    B => (),
  }
}
