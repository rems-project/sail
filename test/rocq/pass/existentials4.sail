default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

union ast = {
  Foo : {'n, 'n in {16,32}. (int, int, int('n), bits('n))},
  Bar : (int, int, {'n, 'n in {16,32}. (int('n), bits('n))}),
}

val foo : forall 'n, 'n in {16,32}. (int, int, int('n), bits('n)) -> int
function foo(i,j,n,v) = i + j + unsigned(v)

val bar : forall 'n, 'n in {16,32}. (int, int, (int('n), bits('n))) -> int
function bar(i,j,(n,v)) = i + j + unsigned(v)

function exec(x : ast) -> int =
  match x {
  Foo(i,j,n,v) => foo(i,j,n,v),
  Bar(i,j,x) => bar(i,j,x),
  }
