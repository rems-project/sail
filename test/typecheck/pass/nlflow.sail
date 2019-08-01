$option -non_lexical_flow

default Order dec

$include <prelude.sail>
$include <exception_basic.sail>

val foo : forall 'n, 'n != 8. int('n) -> unit

function test(xs: bitvector(4, dec)) -> unit = {
  if xs == 0b1000 then {
    throw(Exception())
  };
  let y = unsigned(xs);
  foo(y)
}