default Order dec

$include <flow.sail>

union Foo = {
  Foo : {'n, 'n >= 3. int('n)}
}

function foo(Foo(x as int('x)): Foo) -> unit = {
  _prove(constraint('x >= 4));
}

union Bar('m), 'm <= 100 = {
  Bar : {'n, 'n >= 'm. int('n)}
}

function bar(Bar(x as int('x)) : Bar(23)) -> unit = {
  _prove(constraint('x >= 23));
  ()
}
