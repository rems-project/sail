default Order dec

$include <prelude.sail>

val foo : forall 'n. int('n) -> bits(4)

function foo(n) = {
  0xF
}
