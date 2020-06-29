default Order dec

$include <prelude.sail>

val foo : forall 'n, 'n != 8. int('n) -> unit

function test(y: int) -> unit = {
  if y == 8 then {
    return();
  };
  foo(y)
}
