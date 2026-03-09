default Order dec
$include <prelude.sail>

struct Foo = {
  a : int,
  b : int,
}

function Foo() -> unit = ()

function f(x : Foo) -> Foo = {
  var y: Foo = x;
  y.a = 5;
  y
}

